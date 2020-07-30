use std::num::{Wrapping};

use super::code::{
    self, TestOp, Precision, MemoryLocation, UnaryOp, BinaryOp, DivisionOp,
};
use code::Action::*;
use MemoryLocation::*;
use UnaryOp::*;
use BinaryOp::*;
use DivisionOp::*;
use Precision::*;

use code::R::{RA, RD, RC, RB, RBP, RSI};

pub type Action = code::Action<Memory, Global>;

/** Beetle has only one memory. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Memory {M}

impl code::Alias for Memory {}

/** Beetle's registers. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Global {
    EP,
    A,
    SP,
    RP,
    S0,
    R0,
    Throw,
    Bad,
    NotAddress,
    Memory0,
}

/** Computes the number of bytes in `n` words. */
pub const fn cell_bytes(n: i64) -> i64 { Wrapping(4 * n).0 }

/** The number of bits in a word. */
pub const CELL_BITS: i64 = cell_bytes(8);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {
    Root,
    Dispatch,
    Next,
    Pick,
    Roll,
    Qdup,
    Lshift,
    Rshift,
    Branch,
    Branchi,
    Qbranch,
    Qbranchi,
    Loop,
    Loopi,
    Ploopp,
    Ploopm,
    Ploop,
    Ploopip,
    Ploopim,
    Ploopi,
}

//-----------------------------------------------------------------------------

/** Build a case, in the form that `Beetle::get_code()` returns. */
fn build(
    test_op: TestOp,
    callback: impl FnOnce(&mut Builder),
    state: State,
) -> ((TestOp, Precision), Vec<Action>, State) {
    let mut b = Builder::new();
    callback(&mut b);
    ((test_op, P32), b.0, state)
}


/**
 * A utility for generating action routines.
 *
 * The methods correspond roughly to the cases of type Action. They fill in
 * Beetle-specific default parameters. `load()` and `store()` add code to map
 * Beetle addresses to native addresses. `push()` and `pop()` access Beetle
 * stacks (the native stack is not used).
 */
struct Builder(Vec<Action>);

impl Builder {
    fn new() -> Self {
        Builder(Vec::new())
    }

    fn const_(&mut self, dest: code::R, constant: i64) {
        self.0.push(Constant(P32, dest, constant));
    }

    fn move_(&mut self, dest: code::R, src: code::R) {
        self.0.push(Move(P32, dest, src));
    }

    fn unary(&mut self, op: UnaryOp, dest: code::R, src: code::R) {
        self.0.push(Unary(op, P32, dest, src));
    }

    fn binary(&mut self, op: BinaryOp, dest: code::R, src1: code::R, src2: code::R) {
        self.0.push(Binary(op, P32, dest, src1, src2));
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `RC` is corrupted.
     */
    fn const_binary(&mut self, op: BinaryOp, dest: code::R, src: code::R, constant: i64) {
        assert_ne!(src, RC);
        self.const_(RC, constant);
        self.0.push(Binary(op, P32, dest, src, RC));
    }

    fn load_global(&mut self, dest: code::R, global: Global) {
        self.0.push(LoadGlobal(dest, global));
    }

    fn store_global(&mut self, src: code::R, global: Global) {
        self.0.push(LoadGlobal(src, global));
    }

    /**
     * Compute the native address corresponding to `addr`.
     * `RC` is corrupted.
     */
    fn native_address(&mut self, dest: code::R, addr: code::R) {
        assert_ne!(addr, RC);
        self.load_global(RC, Global::Memory0);
        self.0.push(Binary(Add, P64, dest, RC, addr));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `RC` is corrupted.
     */
    // TODO: Bounds checking.
    fn load(&mut self, dest: code::R, addr: code::R) {
        assert_ne!(addr, RC);
        self.native_address(RC, addr);
        self.0.push(Load(P32, dest, Four(RC, Memory::M)));
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `RC` is corrupted.
     */
    // TODO: Bounds checking.
    fn store(&mut self, src: code::R, addr: code::R) {
        assert_ne!(addr, RC);
        self.native_address(RC, addr);
        self.0.push(Store(src, Four(RC, Memory::M)));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 8 bits.
     * `RC` is corrupted.
     */
    // TODO: Bounds checking.
    fn load_byte(&mut self, dest: code::R, addr: code::R) {
        assert_ne!(addr, RC);
        self.native_address(RC, addr);
        self.0.push(Load(P32, dest, One(RC, Memory::M)));
    }

    /**
     * Compute the native address corresponding to `addr`, and store 8 bits.
     * `RC` is corrupted.
     */
    // TODO: Bounds checking.
    fn store_byte(&mut self, src: code::R, addr: code::R) {
        assert_ne!(addr, RC);
        self.native_address(RC, addr);
        self.0.push(Store(src, One(RC, Memory::M)));
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `RC` is corrupted.
     */
    // TODO: Underflow checking.
    fn pop(&mut self, dest: code::R, addr: code::R) {
        assert_ne!(dest, RC);
        assert_ne!(dest, addr);
        self.load(dest, addr);
        self.const_binary(Add, addr, addr, cell_bytes(1));
    }

    /**
     * Decrement `addr` by `cell_bytes(1)`, then `store()` `src` at `addr`.
     * `RC` is corrupted.
     */
    // TODO: Overflow checking.
    fn push(&mut self, src: code::R, addr: code::R) {
        assert_ne!(src, RC);
        assert_ne!(src, addr);
        self.const_binary(Sub, addr, addr, cell_bytes(1));
        self.store(src, addr);
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Machine;

impl code::Machine for Machine {
    type State = State;
    type Memory = Memory;
    type Global = Global;

    fn get_code(&self, state: Self::State) -> Vec<((TestOp, Precision), Vec<Action>, Self::State)> {
        use Global::{EP as B_EP, A as B_A, SP as B_SP, RP as B_RP};
        match state {
            State::Root => {vec![
                build(TestOp::Always, |b| {
                    b.load_global(RA, B_A);
                    b.const_binary(Asr, RD, RA, 8);
                    b.store_global(RD, B_A);
                }, State::Dispatch),
            ]},
            State::Next => {vec![
                build(TestOp::Always, |b| {
                    b.load_global(RA, B_EP); // FIXME: Add check that EP is valid.
                    b.pop(RD, RA);
                    b.store_global(RD, B_A);
                    b.store_global(RA, B_EP);
                }, State::Root),
            ]},
            State::Pick => {
                let mut pick = Vec::new();
                for u in 0..4 {
                    pick.push(build(TestOp::Eq(RD, u), |b| {
                        b.load_global(RA, B_SP);
                        b.const_binary(Add, RD, RA, cell_bytes(u as i64 + 1));
                        b.load(RD, RD);
                        b.store(RD, RA);
                    }, State::Root));
                }
                pick
            },
            State::Roll => {
                let mut roll = Vec::new();
                for u in 0..4 {
                    roll.push(build(TestOp::Eq(RD, u as i32), |b| {
                        b.const_binary(Add, RBP, RA, cell_bytes(u));
                        b.load(RB, RBP);
                        for v in 0..u {
                            b.const_binary(Add, RSI, RA, cell_bytes(v));
                            b.load(RD, RSI);
                            b.store(RB, RSI);
                            b.move_(RB, RD);
                        }
                        b.store(RB, RBP);
                    }, State::Root));
                }
                roll
            },
            State::Qdup => {vec![
                build(TestOp::Eq(RD, 0), |_| {}, State::Root),
                build(TestOp::Ne(RD, 0), |b| {
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),
            ]},
            State::Lshift => {vec![
                build(TestOp::Ult(RSI, CELL_BITS as i32), |b| {
                    b.binary(Lsl, RD, RD, RSI);
                    b.store(RD, RA);
                }, State::Root),
                build(TestOp::Uge(RSI, CELL_BITS as i32), |b| {
                    b.const_(RD, 0);
                    b.store(RD, RA);
                }, State::Root),
            ]},
            State::Rshift => {vec![
                build(TestOp::Ult(RSI, CELL_BITS as i32), |b| {
                    b.binary(Lsr, RD, RD, RSI);
                    b.store(RD, RA);
                }, State::Root),
                build(TestOp::Uge(RSI, CELL_BITS as i32), |b| {
                    b.const_(RD, 0);
                    b.store(RD, RA);
                }, State::Root),
            ]},
            State::Branch => {vec![
                build(TestOp::Always, |b| {
                    // Load EP from the cell it points to.
                    b.load_global(RA, B_EP);
                    b.load(RA, RA);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                }, State::Next),
            ]},
            State::Branchi => {vec![
                build(TestOp::Always, |b| {
                    b.load_global(RA, B_EP);
                    b.load_global(RD, B_A);
                    b.const_binary(Mul, RD, RD, cell_bytes(1));
                    b.binary(Add, RA, RA, RD);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                }, State::Next),
            ]},
            State::Qbranch => {vec![
                build(TestOp::Eq(RD, 0), |_| {}, State::Branch),
                build(TestOp::Ne(RD, 0), |b| {
                    b.load_global(RA, B_EP);
                    b.const_binary(Add, RA, RA, cell_bytes(1));
                    b.store_global(RA, B_EP);
                }, State::Root),
            ]},
            State::Qbranchi => {vec![
                build(TestOp::Eq(RD, 0), |_| {}, State::Branchi),
                build(TestOp::Ne(RD, 0), |_| {}, State::Root),
            ]},
            State::Loop => {vec![
                build(TestOp::Eq(RB, 0), |b| {
                    // Discard the loop index and limit.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                    // Add 4 to EP.
                    b.load_global(RA, B_EP); // FIXME: Add check that EP is valid.
                    b.const_binary(Add, RA, RA, cell_bytes(1));
                    b.store_global(RA, B_EP);
                }, State::Root),
                build(TestOp::Ne(RB, 0), |_| {}, State::Branch),
            ]},
            State::Loopi => {vec![
                build(TestOp::Eq(RB, 0), |b| {
                    // Discard the loop index and limit.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                }, State::Root),
                build(TestOp::Ne(RB, 0), |_| {}, State::Branchi),
            ]},
            State::Ploopp => {vec![
                build(TestOp::Lt(RBP, 0), |b| {
                    // Discard the loop index and limit.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                    // Add 4 to EP.
                    b.load_global(RA, B_EP); // FIXME: Add check that EP is valid.
                    b.const_binary(Add, RA, RA, cell_bytes(1));
                    b.store_global(RA, B_EP);
                }, State::Root),
                build(TestOp::Ge(RBP, 0), |_| {}, State::Branch),
            ]},
            State::Ploopm => {vec![
                build(TestOp::Lt(RBP, 0), |b| {
                    // Discard the loop index and limit.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                    // Add 4 to EP.
                    b.load_global(RA, B_EP); // FIXME: Add check that EP is valid.
                    b.const_binary(Add, RA, RA, cell_bytes(1));
                    b.store_global(RA, B_EP);
                }, State::Root),
                build(TestOp::Ge(RBP, 0), |_| {}, State::Branch),
            ]},
            State::Ploop => {vec![
                build(TestOp::Ge(RD, 0), |b| {
                    b.unary(Not, RBP, RBP);
                    b.binary(And, RBP, RBP, RB);
                }, State::Ploopp),
                build(TestOp::Lt(RD, 0), |b| {
                    b.unary(Not, RB, RB);
                    b.binary(And, RBP, RBP, RB);
                }, State::Ploopm),
            ]},
            State::Ploopip => {vec![
                build(TestOp::Lt(RBP, 0), |b| {
                    // Discard the loop index and limit.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                }, State::Root),
                build(TestOp::Ge(RBP, 0), |_| {}, State::Branchi),
            ]},
            State::Ploopim => {vec![
                build(TestOp::Lt(RBP, 0), |b| {
                    // Discard the loop index and limit.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                }, State::Root),
                build(TestOp::Ge(RBP, 0), |_| {}, State::Branchi),
            ]},
            State::Ploopi => {vec![
                build(TestOp::Ge(RD, 0), |b| {
                    b.unary(Not, RBP, RBP);
                    b.binary(And, RBP, RBP, RB);
                }, State::Ploopip),
                build(TestOp::Lt(RD, 0), |b| {
                    b.unary(Not, RB, RB);
                    b.binary(And, RBP, RBP, RB);
                }, State::Ploopim),
            ]},
            State::Dispatch => {vec![
                // NEXT
                build(TestOp::Bits(RA, 0xff, 0x00), |_| {}, State::Next),

                // DUP
                build(TestOp::Bits(RA, 0xff, 0x01), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // DROP
                build(TestOp::Bits(RA, 0xff, 0x02), |b| {
                    b.load_global(RA, B_SP);
                    b.const_binary(Add, RA, RA, cell_bytes(1));
                    b.store_global(RA, B_SP);
                }, State::Root),

                // SWAP
                build(TestOp::Bits(RA, 0xff, 0x03), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RSI, RA);
                    b.load(RB, RA);
                    b.store(RSI, RA);
                    b.push(RB, RA);
                }, State::Root),

                // OVER
                build(TestOp::Bits(RA, 0xff, 0x04), |b| {
                    b.load_global(RA, B_SP);
                    b.const_binary(Add, RD, RA, cell_bytes(1));
                    b.load(RB, RD);
                    b.push(RB, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // ROT
                build(TestOp::Bits(RA, 0xff, 0x05), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Add, RBP, RA, cell_bytes(1));
                    b.load(RB, RBP);
                    b.store(RD, RBP);
                    b.const_binary(Add, RBP, RA, cell_bytes(2));
                    b.load(RD, RBP);
                    b.store(RB, RBP);
                    b.store(RD, RA);
                }, State::Root),

                // -ROT
                build(TestOp::Bits(RA, 0xff, 0x06), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Add, RBP, RA, cell_bytes(2));
                    b.load(RB, RBP);
                    b.store(RD, RBP);
                    b.const_binary(Add, RBP, RA, cell_bytes(1));
                    b.load(RD, RBP);
                    b.store(RB, RBP);
                    b.store(RD, RA);
                }, State::Root),

                // TUCK
                build(TestOp::Bits(RA, 0xff, 0x07), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Add, RBP, RA, cell_bytes(1));
                    b.load(RB, RBP);
                    b.store(RD, RBP);
                    b.store(RB, RA);
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // NIP
                build(TestOp::Bits(RA, 0xff, 0x08), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // PICK
                build(TestOp::Bits(RA, 0xff, 0x09), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                }, State::Pick),

                // ROLL
                build(TestOp::Bits(RA, 0xff, 0x0a), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Roll),

                // ?DUP
                build(TestOp::Bits(RA, 0xff, 0x0b), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                }, State::Qdup),

                // >R
                build(TestOp::Bits(RA, 0xff, 0x0c), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_SP);
                    b.load_global(RA, B_RP);
                    b.push(RD, RA);
                    b.store_global(RA, B_RP);
                }, State::Root),

                // R>
                build(TestOp::Bits(RA, 0xff, 0x0d), |b| {
                    b.load_global(RA, B_RP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_RP);
                    b.load_global(RA, B_SP);
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // R@
                build(TestOp::Bits(RA, 0xff, 0x0e), |b| {
                    b.load_global(RA, B_RP);
                    b.load(RD, RA);
                    b.load_global(RA, B_SP);
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // <
                build(TestOp::Bits(RA, 0xff, 0x0f), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Lt, RD, RSI, RD);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // >
                build(TestOp::Bits(RA, 0xff, 0x10), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Lt, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // =
                build(TestOp::Bits(RA, 0xff, 0x11), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Eq, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // <>
                build(TestOp::Bits(RA, 0xff, 0x12), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Eq, RD, RD, RSI);
                    b.unary(Not, RD, RD);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 0<
                build(TestOp::Bits(RA, 0xff, 0x13), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Lt, RD, RD, 0);
                    b.store(RD, RA);
                }, State::Root),

                // 0>
                build(TestOp::Bits(RA, 0xff, 0x14), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_(RSI, 0);
                    b.binary(Lt, RD, RSI, RD);
                    b.store(RD, RA);
                }, State::Root),

                // 0=
                build(TestOp::Bits(RA, 0xff, 0x15), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Eq, RD, RD, 0);
                    b.store(RD, RA);
                }, State::Root),

                // 0<>
                build(TestOp::Bits(RA, 0xff, 0x16), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Eq, RD, RD, 0);
                    b.unary(Not, RD, RD);
                    b.store(RD, RA);
                }, State::Root),

                // U<
                build(TestOp::Bits(RA, 0xff, 0x17), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Ult, RD, RSI, RD);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // U>
                build(TestOp::Bits(RA, 0xff, 0x18), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Ult, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 0
                build(TestOp::Bits(RA, 0xff, 0x19), |b| {
                    b.load_global(RA, B_SP);
                    b.const_(RSI, 0);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 1
                build(TestOp::Bits(RA, 0xff, 0x1a), |b| {
                    b.load_global(RA, B_SP);
                    b.const_(RSI, 1);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // -1
                build(TestOp::Bits(RA, 0xff, 0x1b), |b| {
                    b.load_global(RA, B_SP);
                    b.const_binary(Sub, RA, RA, cell_bytes(1));
                    b.const_(RSI, -1);
                    b.store(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // CELL
                build(TestOp::Bits(RA, 0xff, 0x1c), |b| {
                    b.load_global(RA, B_SP);
                    b.const_binary(Sub, RA, RA, cell_bytes(1));
                    b.const_(RSI, cell_bytes(1));
                    b.store(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // -CELL
                build(TestOp::Bits(RA, 0xff, 0x1d), |b| {
                    b.load_global(RA, B_SP);
                    b.const_binary(Sub, RA, RA, cell_bytes(1));
                    b.const_(RSI, (-Wrapping(cell_bytes(1))).0);
                    b.store(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // +
                build(TestOp::Bits(RA, 0xff, 0x1e), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Add, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // -
                build(TestOp::Bits(RA, 0xff, 0x1f), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Sub, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // >-<
                build(TestOp::Bits(RA, 0xff, 0x20), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Sub, RD, RSI, RD);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 1+
                build(TestOp::Bits(RA, 0xff, 0x21), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Add, RD, RD, 1);
                    b.store(RD, RA);
                }, State::Root),

                // 1-
                build(TestOp::Bits(RA, 0xff, 0x22), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Sub, RD, RD, 1);
                    b.store(RD, RA);
                }, State::Root),

                // CELL+
                build(TestOp::Bits(RA, 0xff, 0x23), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Add, RD, RD, cell_bytes(1));
                    b.store(RD, RA);
                }, State::Root),

                // CELL-
                build(TestOp::Bits(RA, 0xff, 0x24), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Sub, RD, RD, cell_bytes(1));
                    b.store(RD, RA);
                }, State::Root),

                // *
                build(TestOp::Bits(RA, 0xff, 0x25), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Mul, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // /
                build(TestOp::Bits(RA, 0xff, 0x26), |_| {
                    // TODO
                }, State::Root),

                // MOD
                build(TestOp::Bits(RA, 0xff, 0x27), |_| {
                    // TODO
                }, State::Root),

                // /MOD
                build(TestOp::Bits(RA, 0xff, 0x28), |_| {
                    // TODO
                }, State::Root),

                // U/MOD
                build(TestOp::Bits(RA, 0xff, 0x29), |b| {
                    b.load_global(RB, B_SP);
                    b.pop(RD, RB);
                    b.load(RA, RB);
                    b.0.push(Division(UnsignedDivMod, P32, RA, RD, RA, RD));
                    b.store(RD, RB);
                    b.push(RA, RB);
                }, State::Root),

                // S/REM
                build(TestOp::Bits(RA, 0xff, 0x2a), |b| {
                    b.load_global(RB, B_SP);
                    b.pop(RD, RB);
                    b.load(RA, RB);
                    b.0.push(Division(SignedDivMod, P32, RA, RD, RA, RD));
                    b.store(RD, RB);
                    b.push(RA, RB);
                }, State::Root),

                // 2/
                build(TestOp::Bits(RA, 0xff, 0x2b), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Asr, RD, RD, 1);
                    b.store(RD, RA);
                }, State::Root),

                // CELLS
                build(TestOp::Bits(RA, 0xff, 0x2c), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Mul, RD, RD, cell_bytes(1));
                    b.store(RD, RA);
                }, State::Root),

                // ABS
                build(TestOp::Bits(RA, 0xff, 0x2d), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.unary(Abs, RD, RD);
                    b.store(RD, RA);
                }, State::Root),

                // NEGATE
                build(TestOp::Bits(RA, 0xff, 0x2e), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.unary(Negate, RD, RD);
                    b.store(RD, RA);
                }, State::Root),

                // MAX
                build(TestOp::Bits(RA, 0xff, 0x2f), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Max, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // MIN
                build(TestOp::Bits(RA, 0xff, 0x30), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Min, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // INVERT
                build(TestOp::Bits(RA, 0xff, 0x31), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.unary(Not, RD, RD);
                    b.store(RD, RA);
                }, State::Root),

                // AND
                build(TestOp::Bits(RA, 0xff, 0x32), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(And, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // OR
                build(TestOp::Bits(RA, 0xff, 0x33), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Or, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // XOR
                build(TestOp::Bits(RA, 0xff, 0x34), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.binary(Xor, RD, RD, RSI);
                    b.store(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // LSHIFT
                build(TestOp::Bits(RA, 0xff, 0x35), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Lshift),

                // RSHIFT
                build(TestOp::Bits(RA, 0xff, 0x36), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.load(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Rshift),

                // 1LSHIFT
                build(TestOp::Bits(RA, 0xff, 0x37), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Lsl, RD, RD, 1);
                    b.store(RD, RA);
                }, State::Root),

                // 1RSHIFT
                build(TestOp::Bits(RA, 0xff, 0x38), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.const_binary(Lsr, RD, RD, 1);
                    b.store(RD, RA);
                }, State::Root),

                // @
                build(TestOp::Bits(RA, 0xff, 0x39), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.load(RD, RD);
                    b.store(RD, RA);
                }, State::Root),

                // !
                build(TestOp::Bits(RA, 0xff, 0x3a), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.pop(RB, RA);
                    b.store(RB, RD);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // C@
                build(TestOp::Bits(RA, 0xff, 0x3b), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RD, RA);
                    b.load_byte(RD, RD);
                    b.store(RD, RA);
                }, State::Root),

                // C!
                build(TestOp::Bits(RA, 0xff, 0x3c), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.pop(RB, RA);
                    b.store_byte(RB, RD);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // +!
                build(TestOp::Bits(RA, 0xff, 0x3d), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.pop(RB, RA);
                    b.load(RBP, RD);
                    b.binary(Add, RB, RBP, RB);
                    b.store(RB, RD);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // SP@
                build(TestOp::Bits(RA, 0xff, 0x3e), |b| {
                    b.load_global(RA, B_SP);
                    b.move_(RSI, RA);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // SP!
                build(TestOp::Bits(RA, 0xff, 0x3f), |b| {
                    b.load_global(RA, B_SP);
                    b.load(RA, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // RP@
                build(TestOp::Bits(RA, 0xff, 0x40), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, B_RP);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // RP!
                build(TestOp::Bits(RA, 0xff, 0x41), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RD, B_RP);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // EP@
                build(TestOp::Bits(RA, 0xff, 0x42), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, B_EP);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // S0@
                build(TestOp::Bits(RA, 0xff, 0x43), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, Global::S0);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // S0!
                build(TestOp::Bits(RA, 0xff, 0x44), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RD, Global::S0);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // R0@
                build(TestOp::Bits(RA, 0xff, 0x45), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, Global::R0);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // R0!
                build(TestOp::Bits(RA, 0xff, 0x46), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RD, Global::R0);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 'THROW@
                build(TestOp::Bits(RA, 0xff, 0x47), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, Global::Throw);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 'THROW!
                build(TestOp::Bits(RA, 0xff, 0x48), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RD, Global::Throw);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // MEMORY@
                build(TestOp::Bits(RA, 0xff, 0x49), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, Global::Memory0);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // 'BAD@
                build(TestOp::Bits(RA, 0xff, 0x4a), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, Global::Bad);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // -ADDRESS@
                build(TestOp::Bits(RA, 0xff, 0x4b), |b| {
                    b.load_global(RA, B_SP);
                    b.load_global(RSI, Global::NotAddress);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // BRANCH
                build(TestOp::Bits(RA, 0xff, 0x4c), |_| {}, State::Branch),

                // BRANCHI
                build(TestOp::Bits(RA, 0xff, 0x4d), |_| {}, State::Branchi),

                // ?BRANCH
                build(TestOp::Bits(RA, 0xff, 0x4e), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Qbranch),

                // ?BRANCHI
                build(TestOp::Bits(RA, 0xff, 0x4f), |b| {
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Qbranchi),

                // EXECUTE
                build(TestOp::Bits(RA, 0xff, 0x50), |b| {
                    // Push EP onto the return stack.
                    b.load_global(RD, B_RP);
                    b.load_global(RA, B_EP);
                    b.push(RA, RD);
                    b.store_global(RD, B_RP);
                    // Put a-addr1 into EP.
                    b.load_global(RD, B_SP);
                    b.pop(RA, RD);
                    b.store_global(RD, B_SP);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                }, State::Next),

                // @EXECUTE
                build(TestOp::Bits(RA, 0xff, 0x51), |b| {
                    // Push EP onto the return stack.
                    b.load_global(RD, B_RP);
                    b.load_global(RA, B_EP);
                    b.push(RA, RD);
                    b.store_global(RD, B_RP);
                    // Put the contents of a-addr1 into EP.
                    b.load_global(RD, B_SP);
                    b.pop(RA, RD);
                    b.store_global(RD, B_SP);
                    b.load(RA, RA);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                }, State::Next),

                // CALL
                build(TestOp::Bits(RA, 0xff, 0x52), |b| {
                    // Push EP+4 onto the return stack.
                    b.load_global(RD, B_RP);
                    b.load_global(RA, B_EP);
                    b.const_binary(Add, RA, RA, cell_bytes(1));
                    b.push(RA, RD);
                    b.store_global(RD, B_RP);
                }, State::Branch),

                // CALLI
                build(TestOp::Bits(RA, 0xff, 0x53), |b| {
                    // Push EP onto the return stack.
                    b.load_global(RD, B_RP);
                    b.load_global(RA, B_EP);
                    b.push(RA, RD);
                    b.store_global(RD, B_RP);
                }, State::Branchi),

                // EXIT
                build(TestOp::Bits(RA, 0xff, 0x54), |b| {
                    // Put a-addr into EP.
                    b.load_global(RD, B_RP);
                    b.pop(RA, RD);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                    b.store_global(RD, B_RP);
                }, State::Next),

                // (DO)
                build(TestOp::Bits(RA, 0xff, 0x55), |b| {
                    // Pop two items from SP.
                    b.load_global(RA, B_SP);
                    b.pop(RSI, RA);
                    b.pop(RB, RA);
                    b.store_global(RA, B_SP);
                    // Push two items to RP.
                    b.load_global(RA, B_RP);
                    b.push(RB, RA);
                    b.push(RSI, RA);
                    b.store_global(RA, B_RP);
                }, State::Root),

                // (LOOP)
                build(TestOp::Bits(RA, 0xff, 0x56), |b| {
                    // Load the index and limit from RP.
                    b.load_global(RA, B_RP);
                    b.pop(RB, RA);
                    b.load(RSI, RA);
                    // Update the index.
                    b.const_binary(Add, RB, RB, 1);
                    b.push(RB, RA);
                    b.binary(Sub, RB, RB, RSI);
                }, State::Loop),

                // (LOOP)I
                build(TestOp::Bits(RA, 0xff, 0x57), |b| {
                    // Load the index and limit from RP.
                    b.load_global(RA, B_RP);
                    b.pop(RB, RA);
                    b.load(RSI, RA);
                    // Update the index.
                    b.const_binary(Add, RB, RB, 1);
                    b.push(RB, RA);
                    b.binary(Sub, RB, RB, RSI);
                }, State::Loopi),

                // (+LOOP)
                build(TestOp::Bits(RA, 0xff, 0x58), |b| {
                    // Pop the step from SP.
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_SP);
                    // Load the index and limit from RP.
                    b.load_global(RA, B_RP);
                    b.pop(RB, RA);
                    b.load(RSI, RA);
                    // Update the index.
                    b.binary(Add, RBP, RB, RD);
                    b.push(RBP, RA);
                    // Compute the differences between old and new indexes and limit.
                    b.binary(Sub, RB, RB, RSI);
                    b.binary(Sub, RBP, RBP, RSI);
                }, State::Ploop),

                // (+LOOP)I
                build(TestOp::Bits(RA, 0xff, 0x59), |b| {
                    // Pop the step from SP.
                    b.load_global(RA, B_SP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_SP);
                    // Load the index and limit from RP.
                    b.load_global(RA, B_RP);
                    b.pop(RB, RA);
                    b.load(RSI, RA);
                    // Update the index.
                    b.binary(Add, RBP, RB, RD);
                    b.push(RBP, RA);
                    // Compute the differences between old and new indexes and limit.
                    b.binary(Sub, RB, RB, RSI);
                    b.binary(Sub, RBP, RBP, RSI);
                }, State::Ploopi),

                // UNLOOP
                build(TestOp::Bits(RA, 0xff, 0x5a), |b| {
                    // Discard two items from RP.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.store_global(RA, B_RP);
                }, State::Root),

                // J
                build(TestOp::Bits(RA, 0xff, 0x5b), |b| {
                    // Push the third item of RP to SP.
                    b.load_global(RA, B_RP);
                    b.const_binary(Add, RA, RA, cell_bytes(2));
                    b.load(RSI, RA);
                    b.load_global(RA, B_SP);
                    b.push(RSI, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // (LITERAL)
                build(TestOp::Bits(RA, 0xff, 0x5c), |b| {
                    // Load RD from cell pointed to by EP, and add 4 to EP.
                    b.load_global(RA, B_EP);
                    b.pop(RD, RA);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                    // Push RD to the stack.
                    b.load_global(RA, B_SP);
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Root),

                // (LITERAL)I
                build(TestOp::Bits(RA, 0xff, 0x5d), |b| {
                    // Push A to the stack.
                    b.load_global(RD, B_A);
                    b.load_global(RA, B_SP);
                    b.push(RD, RA);
                    b.store_global(RA, B_SP);
                }, State::Next),

                // THROW
                build(TestOp::Bits(RA, 0xff, 0x5e), |b| {
                    // Set 'BAD to EP
                    b.load_global(RA, B_EP);
                    b.store_global(RA, Global::Bad);
                    // Load EP from 'THROW
                    b.load_global(RA, Global::Throw);
                    b.load(RA, RA);
                    b.store_global(RA, B_EP); // FIXME: Add check that EP is valid.
                }, State::Next),
            ]},
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Root]
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    pub fn ackermann_object() -> Vec<u32> {
        // Forth source:
        // : ACKERMANN   ( m n -- result )
        // OVER 0= IF                  \ m = 0
        //     NIP 1+                  \ n+1
        // ELSE
        //     DUP 0= IF               \ n = 0
        //         DROP 1- 1 RECURSE   \ A(m-1, 1)
        //     ELSE
        //         OVER 1- -ROT        \ m-1 m n
        //         1- RECURSE          \ m-1 A(m, n-1)
        //         RECURSE             \ A(m-1, A(m, n-1))
        //     THEN
        // THEN ;

        // Beetle assembler:
        // $00: OVER
        //      0=
        // $04: ?BRANCHI $10
        // $08: NIP
        //      1+
        // $0C: BRANCHI $30
        // $10: DUP
        //      0=
        // $14: ?BRANCHI $24
        // $18: DROP
        //      1-
        //      1
        // $1C: CALLI $0
        // $20: BRANCHI $30
        // $24: OVER
        //      1-
        //      -ROT
        //      1-
        // $28: CALLI $0
        // $2C: CALLI $0
        // $30: EXIT

        // Beetle object code:
        vec![
            0x00001504, 0x0000024F, 0x00002108, 0x0000084D,
            0x00001501, 0x0000034F, 0x001A2202, 0xFFFFF853,
            0x0000034D, 0x22062204, 0xFFFFF553, 0xFFFFF453,
            0x00000054,
        ]
    }
}