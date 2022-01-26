/*!
 * A utility for generating Mijit code that understands Beetle's conventions.
 */

use std::collections::{HashSet};
use memoffset::{offset_of};

use super::code::{
    self, Precision, UnaryOp, BinaryOp, Width, Register, Global,
    Action, Marshal, EBB, Ending,
};
use Precision::*;
use BinaryOp::*;
use Width::*;
use Action::*;
use super::{Registers, CELL, TEMP, BEP, BI, BA, BSP, BRP, M0};

/**
 * Beetle's address space is unified, so we always use the same `AliasMask`.
 */
const AM_MEMORY: code::AliasMask = code::AliasMask(0x1);

/**
 * Beetle's registers are not in Beetle's memory, so we use a different
 * `AliasMask`.
 */
const AM_REGISTER: code::AliasMask = code::AliasMask(0x2);

/**
 * A utility for generating action routines.
 *
 * The methods correspond roughly to the cases of type Action. They fill in
 * Beetle-specific default parameters. `load()` and `store()` add code to map
 * Beetle addresses to native addresses. `push()` and `pop()` access Beetle
 * stacks (the native stack is not used).
 *
 * For examples, see tests.
 */
pub struct Builder(Vec<Action>);

impl Builder {
    pub fn new() -> Self {
        Builder(Vec::new())
    }

    pub fn const_(&mut self, dest: Register, constant: u32) {
        self.0.push(Constant(P32, dest, constant as i64));
    }

    pub fn const64(&mut self, dest: Register, constant: u64) {
        self.0.push(Constant(P64, dest, constant as i64));
    }

    /**
     * Apply 32-bit `op` to `src`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn unary(&mut self, op: UnaryOp, dest: Register, src: Register) {
        self.0.push(Unary(op, P32, dest, src.into()));
    }

    /**
     * Apply 32-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn binary(&mut self, op: BinaryOp, dest: Register, src1: Register, src2: Register) {
        self.0.push(Binary(op, P32, dest, src1.into(), src2.into()));
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    pub fn const_binary(&mut self, op: BinaryOp, dest: Register, src: Register, constant: u32) {
        assert_ne!(src, TEMP);
        self.const_(TEMP, constant);
        self.binary(op, dest, src, TEMP);
    }

    /** Compute the native address corresponding to `addr`. */
    pub fn native_address(&mut self, dest: Register, addr: Register) {
        self.0.push(Binary(Add, P64, dest, M0.into(), addr.into()));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `TEMP` is corrupted.
     */
    pub fn load(&mut self, dest: Register, addr: Register) {
        self.native_address(TEMP, addr);
        self.0.push(Load(dest, (TEMP.into(), Four), AM_MEMORY));
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    pub fn store(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        self.native_address(TEMP, addr);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_MEMORY));
    }

    /** Compute the native address `Global(0) + offset`. */
    pub fn register_address(&mut self, dest: Register, offset: usize) {
        self.const64(dest, offset as u64);
        self.0.push(Binary(Add, P64, dest, Global(0).into(), dest.into()));
    }

    /**
     * Load 32 bits from host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    pub fn load_register(&mut self, dest: Register, offset: usize) {
        self.register_address(TEMP, offset);
        self.0.push(Load(dest, (TEMP.into(), Four), AM_REGISTER));
    }

    /**
     * Store 32 bits to host address `Global(0) + offset`.
     * `TEMP` is corrupted.
     */
    pub fn store_register(&mut self, src: Register, offset: usize) {
        self.register_address(TEMP, offset);
        self.0.push(Store(TEMP, src.into(), (TEMP.into(), Four), AM_REGISTER));
    }

    pub fn load_global(&mut self, dest: Register, src: Global) {
        self.0.push(Move(dest.into(), src.into()))
    }

    pub fn store_global(&mut self, src: Register, dest: Global) {
        self.0.push(Move(dest.into(), src.into()))
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    pub fn pop(&mut self, dest: Register, addr: Register) {
        assert_ne!(dest, addr);
        assert_ne!(dest, TEMP);
        self.load(dest, addr);
        self.const_binary(Add, addr, addr, CELL);
    }

    /**
     * Decrement `addr` by `CELL`, then `store()` `src` at `addr`.
     * `TEMP` is corrupted.
     */
    pub fn push(&mut self, src: Register, addr: Register) {
        assert_ne!(src, TEMP);
        assert_ne!(src, addr);
        self.const_binary(Sub, addr, addr, CELL);
        self.store(src, addr);
    }

    /** Returns all the [`Action`]s that this `Builder` has accumulated. */
    pub fn finish(self) -> Box<[Action]> {
        self.0.into()
    }
}

/**
 * Build a [`Case`], in the form that `Machine::code()` returns.
 *
 * For examples, see tests.
 */
pub fn build<L: Clone>(
    callback: impl FnOnce(&mut Builder),
    ending: Ending<L>,
) -> EBB<L> {
    let mut b = Builder::new();
    callback(&mut b);
    EBB {actions: b.0, ending}
}

/** Returns the offset of `$field`. */
macro_rules! register {
    ($field: ident) => {
        offset_of!(Registers, $field)
    }
}

/** Build a `Marshal` given the subset of {BA, BI} that are dead. */
pub fn marshal(dead_registers: impl IntoIterator<Item=Register>) -> Marshal {
    let mut dead_registers: HashSet<Register> = dead_registers.into_iter().collect();
    let prologue = {
        let mut b = Builder::new();
        b.load_register(BEP, register!(ep));
        b.load_register(BI, register!(i));
        b.load_register(BA, register!(a));
        b.load_register(BSP, register!(sp));
        b.load_register(BRP, register!(rp));
        b.load_global(M0, Global(1));
        b.finish()
    };
    let epilogue = {
        let mut b = Builder::new();
        for v in [BA, BI] {
            if dead_registers.remove(&v) {
                b.const64(v, 0xDEADDEADDEADDEADu64);
            }
        }
        b.store_register(BEP, register!(ep));
        b.store_register(BI, register!(i));
        b.store_register(BA, register!(a));
        b.store_register(BSP, register!(sp));
        b.store_register(BRP, register!(rp));
        b.store_global(M0, Global(1));
        b.finish()
    };
    assert_eq!(dead_registers.len(), 0);
    Marshal {prologue, epilogue}
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use super::code::{Switch};
    use super::super::{R2, R3, BI, BEP, BSP};

    /** Illustrate [`Builder`]. */
    #[test]
    fn builder() {
        let mut b = Builder::new();
        b.load_register(BEP, 16);
        // ...more code...
        let _ = b.finish();
    }

    /** Illustrate [`build()`]. */
    #[test]
    fn build() {
        let _ = Switch::if_(
            BI.into(), // `Ult(R2, CELL_BITS)`
            super::build(|b| {
                b.binary(Lsl, R2, R3, R2);
                b.store(R2, BSP);
            }, Ending::Leaf(0)),
            super::build(|b| {
                b.const_(R2, 0);
                b.store(R2, BSP);
            }, Ending::Leaf(0)),
        );
    }
}
