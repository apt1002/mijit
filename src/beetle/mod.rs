//! A partial implementation of the [Beetle] virtual machine in Mijit.
//! This serves as an illustrative example as an integration test.
//! 
//! [Beetle]: https://github.com/rrthomas/beetle

use memoffset::{offset_of};

use super::code::{self, UnaryOp, BinaryOp, Width, Register, REGISTERS, Global, Marshal, Switch};
use UnaryOp::*;
use BinaryOp::*;
use Width::*;
use super::target::{Word, Target};
use super::jit::{EntryId, Jit};
use super::code::builder::{build, build_block, Builder};

mod registers;
pub use registers::{Registers};

/// The number of bytes in a cell.
pub const CELL: i32 = 4;

/// The number of bits in a word.
pub const CELL_BITS: i32 = CELL * 8;

//-----------------------------------------------------------------------------

const R1: Register = REGISTERS[1];
const R2: Register = REGISTERS[2];
const R3: Register = REGISTERS[3];
const BEP: Register = REGISTERS[4];
const BI: Register = REGISTERS[5];
const BA: Register = REGISTERS[6];
const BSP: Register = REGISTERS[7];
const BRP: Register = REGISTERS[8];
const M0: Register = REGISTERS[9];

/// Returns the address of `Registers.$field`.
macro_rules! register {
    ($field: ident) => {
        (Global(0), offset_of!(Registers, $field) as i64)
    }
}

/// The return code used to indicate normal exit from the hot code.
const NOT_IMPLEMENTED: i64 = 0;
/// Dummy return code which should never actually occur.
const UNDEFINED: i64 = i64::MAX;

/// Beetle's address space is unified, so we always use the same `AliasMask`.
const AM_MEMORY: code::AliasMask = code::AliasMask(0x1);

/// Beetle's registers are not in Beetle's memory, so we use a different
/// `AliasMask`.
const AM_REGISTER: code::AliasMask = code::AliasMask(0x2);

//-----------------------------------------------------------------------------

/// Computes into `BI` the native address corresponding to `addr`.
fn native_address(b: &mut Builder<EntryId>, addr: Register) {
    b.binary64(Add, BI, M0, addr);
}

/// Loads `dest` from `addr`. `BI` is corrupted.
fn load(b: &mut Builder<EntryId>, dest: Register, addr: Register) {
    native_address(b, addr);
    b.load(dest, (BI, 0), Four, AM_MEMORY);
}

/// Stores `dest` at `addr`. `BI` is corrupted.
fn store(b: &mut Builder<EntryId>, src: Register, addr: Register) {
    native_address(b, addr);
    b.store(src, (BI, 0), Four, AM_MEMORY);
}

/// Pops `dest` from the stack at `sp`. `BI` is corrupted.
fn pop(b: &mut Builder<EntryId>, dest: Register, sp: Register) {
    load(b, dest, sp);
    b.const_binary32(Add, sp, sp, CELL);
}

/// Pushes `src` to the stack at `sp`. `BI` is corrupted.
fn push(b: &mut Builder<EntryId>, src: Register, sp: Register) {
    b.const_binary32(Sub, sp, sp, CELL);
    store(b, src, sp);
}

/// The performance-critical part of the virtual machine.
#[derive(Debug)]
pub struct Beetle<T: Target> {
    pub jit: Jit<T>,
    pub root: EntryId,
}

impl<T: Target> Beetle<T> {
    #[allow(clippy::too_many_lines)]
    pub fn new(target: T) -> Self {
        let mut jit = Jit::new(target, 2);
        let marshal = Marshal {
            prologue: build_block(&mut |b| {
                b.load(BEP, register!(ep), Four, AM_REGISTER);
                b.load(BI, register!(i), Four, AM_REGISTER);
                b.load(BA, register!(a), Four, AM_REGISTER);
                b.load(BSP, register!(sp), Four, AM_REGISTER);
                b.load(BRP, register!(rp), Four, AM_REGISTER);
                b.move_(M0, Global(1));
            }),
            epilogue: build_block(&mut |b| {
                b.store(BEP, register!(ep), Four, AM_REGISTER);
                b.store(BI, register!(i), Four, AM_REGISTER);
                b.store(BA, register!(a), Four, AM_REGISTER);
                b.store(BSP, register!(sp), Four, AM_REGISTER);
                b.store(BRP, register!(rp), Four, AM_REGISTER);
                b.move_(Global(1), M0);
            }),
        };
        let root = jit.new_entry(&marshal, UNDEFINED);

        // Immediate branch.
        let branchi = jit.new_entry(&marshal, UNDEFINED);
        jit.define(branchi, &build(&mut |mut b| {
            b.const_binary32(Mul, R1, BA, CELL);
            b.binary32(Add, BEP, BEP, R1);
            pop(&mut b, BA, BEP);
            b.jump(root)
        }));
        
        // Not implemented.
        let not_implemented2 = jit.new_entry(&marshal, NOT_IMPLEMENTED);
        let not_implemented = jit.new_entry(&marshal, UNDEFINED);
        jit.define(not_implemented, &build(&mut |mut b| {
            b.const_binary32(Lsl, BA, BA, 8);
            b.binary32(Or, BA, BA, BI);
            b.jump(not_implemented2)
        }));

        // Main dispatch loop.
        jit.define(root, &build(&mut |mut b| {
            b.const_binary32(And, BI, BA, 0xFF);
            b.const_binary32(Asr, BA, BA, 8);
            b.switch(BI, Switch::new(
                Box::new([
                    // NEXT
                    build(&mut |mut b| {
                        pop(&mut b, BA, BEP);
                        b.jump(root)
                    }),

                    // DUP
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        push(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // DROP
                    build(&mut |mut b| {
                        b.const_binary32(Add, BSP, BSP, CELL);
                        b.jump(root)
                    }),

                    // SWAP
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        store(&mut b, R2, BSP);
                        push(&mut b, R3, BSP);
                        b.jump(root)
                    }),

                    // OVER
                    build(&mut |mut b| {
                        b.const_binary32(Add, R1, BSP, CELL);
                        load(&mut b, R2, R1);
                        push(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // ROT
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Add, R1, BSP, CELL);
                        load(&mut b, R3, R1);
                        store(&mut b, R2, R1);
                        b.const_binary32(Add, R1, BSP, 2 * CELL);
                        load(&mut b, R2, R1);
                        store(&mut b, R3, R1);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // -ROT
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Add, R1, BSP, 2 * CELL);
                        load(&mut b, R3, R1);
                        store(&mut b, R2, R1);
                        b.const_binary32(Add, R1, BSP, CELL);
                        load(&mut b, R2, R1);
                        store(&mut b, R3, R1);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // TUCK
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Add, R1, BSP, CELL);
                        load(&mut b, R3, R1);
                        store(&mut b, R2, R1);
                        store(&mut b, R3, BSP);
                        push(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // NIP
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // PICK
                    build(&mut |b| { b.jump(not_implemented) }),

                    // ROLL
                    build(&mut |b| { b.jump(not_implemented) }),

                    // ?DUP
                    build(&mut |b| { b.jump(not_implemented) }),

                    // >R
                    build(&mut |b| { b.jump(not_implemented) }),

                    // R>
                    build(&mut |b| { b.jump(not_implemented) }),

                    // R@
                    build(&mut |b| { b.jump(not_implemented) }),

                    // <
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Lt, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // >
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Lt, R2, R2, R3);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // =
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Eq, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // <>
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Eq, R2, R3, R2);
                        b.unary32(Not, R2, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 0<
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Lt, R2, R2, 0);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 0>
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_(R3, 0);
                        b.binary32(Lt, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 0=
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Eq, R2, R2, 0);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 0<>
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Eq, R2, R2, 0);
                        b.unary32(Not, R2, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // U<
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Ult, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // U>
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Ult, R2, R2, R3);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 0
                    build(&mut |mut b| {
                        b.const_(R2, 0);
                        push(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 1
                    build(&mut |mut b| {
                        b.const_(R2, 1);
                        push(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // -1
                    build(&mut |mut b| {
                        b.const_(R2, -1i32 as u32 as i64);
                        push(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // CELL
                    build(&mut |b| { b.jump(not_implemented) }),

                    // -CELL
                    build(&mut |b| { b.jump(not_implemented) }),

                    // +
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Add, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // -
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Sub, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // >-<
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Sub, R2, R2, R3);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 1+
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Add, R2, R2, 1);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // 1-
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.const_binary32(Sub, R2, R2, 1);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // CELL+
                    build(&mut |b| { b.jump(not_implemented) }),

                    // CELL-
                    build(&mut |b| { b.jump(not_implemented) }),

                    // *
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Mul, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // /
                    build(&mut |b| { b.jump(not_implemented) }),

                    // MOD
                    build(&mut |b| { b.jump(not_implemented) }),

                    // /MOD
                    build(&mut |b| { b.jump(not_implemented) }),

                    // U/MOD
                    build(&mut |b| { b.jump(not_implemented) }),

                    // S/REM
                    build(&mut |b| { b.jump(not_implemented) }),

                    // 2/
                    build(&mut |b| { b.jump(not_implemented) }),

                    // CELLS
                    build(&mut |b| { b.jump(not_implemented) }),

                    // ABS
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.unary32(Abs, R2, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // NEGATE
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.unary32(Negate, R2, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // MAX
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Max, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // MIN
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        load(&mut b, R3, BSP);
                        b.binary32(Min, R2, R3, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // INVERT
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        b.unary32(Not, R2, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // AND
                    build(&mut |b| { b.jump(not_implemented) }),

                    // OR
                    build(&mut |b| { b.jump(not_implemented) }),

                    // XOR
                    build(&mut |b| { b.jump(not_implemented) }),

                    // LSHIFT
                    build(&mut |b| { b.jump(not_implemented) }),

                    // RSHIFT
                    build(&mut |b| { b.jump(not_implemented) }),

                    // 1LSHIFT
                    build(&mut |b| { b.jump(not_implemented) }),

                    // 1RSHIFT
                    build(&mut |b| { b.jump(not_implemented) }),

                    // @
                    build(&mut |mut b| {
                        load(&mut b, R2, BSP);
                        load(&mut b, R2, R2);
                        store(&mut b, R2, BSP);
                        b.jump(root)
                    }),

                    // !
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        pop(&mut b, R3, BSP);
                        store(&mut b, R3, R2);
                        b.jump(root)
                    }),

                    // C@
                    build(&mut |b| { b.jump(not_implemented) }),

                    // C!
                    build(&mut |b| { b.jump(not_implemented) }),

                    // +!
                    build(&mut |mut b| {
                        pop(&mut b, R2, BSP);
                        pop(&mut b, R3, BSP);
                        load(&mut b, R1, R2);
                        b.binary32(Add, R3, R1, R3);
                        store(&mut b, R3, R2);
                        b.jump(root)
                    }),

                    // SP@
                    build(&mut |b| { b.jump(not_implemented) }),

                    // SP!
                    build(&mut |b| { b.jump(not_implemented) }),

                    // RP@
                    build(&mut |b| { b.jump(not_implemented) }),

                    // RP!
                    build(&mut |b| { b.jump(not_implemented) }),

                    // BRANCH
                    build(&mut |b| { b.jump(not_implemented) }),

                    // BRANCHI
                    build(&mut |b| { b.jump(branchi) }),

                    // ?BRANCH
                    build(&mut |b| { b.jump(not_implemented) }),

                    // ?BRANCHI
                    build(&mut |mut b| {
                        pop(&mut b, BI, BSP);
                        b.if_(BI,
                            build(&mut |mut b| {
                                pop(&mut b, BA, BEP);
                                b.jump(root)
                            }),
                            build(&mut |b| { b.jump(branchi) }),
                        )
                    }),

                    // EXECUTE
                    build(&mut |b| { b.jump(not_implemented) }),

                    // @EXECUTE
                    build(&mut |b| { b.jump(not_implemented) }),

                    // CALL
                    build(&mut |b| { b.jump(not_implemented) }),

                    // CALLI
                    build(&mut |mut b| {
                        push(&mut b, BEP, BRP);
                        b.jump(branchi)
                    }),

                    // EXIT
                    build(&mut |mut b| {
                        pop(&mut b, BEP, BRP);
                        pop(&mut b, BA, BEP);
                        b.jump(root)
                    }),

                    // (DO)
                    build(&mut |b| { b.jump(not_implemented) }),

                    // (LOOP)
                    build(&mut |b| { b.jump(not_implemented) }),

                    // (LOOP)I
                    build(&mut |b| { b.jump(not_implemented) }),

                    // (+LOOP)
                    build(&mut |b| { b.jump(not_implemented) }),

                    // (+LOOP)I
                    build(&mut |b| { b.jump(not_implemented) }),

                    // UNLOOP
                    build(&mut |b| { b.jump(not_implemented) }),

                    // J
                    build(&mut |b| { b.jump(not_implemented) }),

                    // (LITERAL)
                    build(&mut |b| { b.jump(not_implemented) }),

                    // (LITERAL)I
                    build(&mut |mut b| {
                        push(&mut b, BA, BSP);
                        pop(&mut b, BA, BEP);
                        b.jump(root)
                    }),
                ]),
                build(&mut |b| { b.jump(not_implemented) }),
            ))
        }));

        Self {jit, root}
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        self.jit.global_mut(global)
    }

    pub unsafe fn run(&mut self, registers: &mut Registers, m0: &mut[u32]) {
        *self.jit.global_mut(Global(0)) = Word {mp: (registers as *mut Registers).cast()};
        *self.jit.global_mut(Global(1)) = Word {mp: (m0.as_mut_ptr()).cast()};
        let result = self.jit.run(self.root);
        assert_eq!(result, Word {s: NOT_IMPLEMENTED});
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests;
