use std::num::{Wrapping};

use super::code::{self, TestOp, Precision, UnaryOp, BinaryOp, Width, Action, Value, Register};
use Precision::*;
use UnaryOp::*;
use BinaryOp::*;
use Width::*;
use Action::*;
use Value::*;
use Register::{RA, RD, RB, RBP, RSI};

const TEMP: Register = code::Register::RDI;

/** Beetle's registers. */
pub mod reg {
    use super::{Value, Slot};
    pub const EP: Value = Slot(0);
    pub const A: Value = Slot(1);
    pub const SP: Value = Slot(2);
    pub const RP: Value = Slot(3);
    pub const S0: Value = Slot(4);
    pub const R0: Value = Slot(5);
    pub const THROW: Value = Slot(6);
    pub const BAD: Value = Slot(7);
    pub const NOT_ADDRESS: Value = Slot(8);
    pub const MEMORY: Value = Slot(9);
}

const NUM_REGISTERS: usize = 10;

const S_A: Value = Slot(NUM_REGISTERS + 0);
const STACK_0: Value = Slot(NUM_REGISTERS + 1);
const STACK_1: Value = Slot(NUM_REGISTERS + 2);
const LOOP_FLAG: Value = Slot(NUM_REGISTERS + 3);
const LOOP_STEP: Value = Slot(NUM_REGISTERS + 4);
const LOOP_NEW: Value = Slot(NUM_REGISTERS + 5);
const LOOP_OLD: Value = Slot(NUM_REGISTERS + 6);

/** Beetle's address space is unified, so we always use the same AliasMask. */
const MEMORY: code::AliasMask = code::AliasMask(0x1);

/** Computes the number of bytes in `n` cells. */
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
    Halt,
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


trait IntoValue: Copy + Into<Value> {}

impl<T: Copy + Into<Value>> IntoValue for T {}

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

    fn const_(&mut self, dest: impl IntoValue, constant: i64) {
        self.0.push(Constant(P32, dest.into(), constant));
    }

    fn move_(&mut self, dest: impl IntoValue, src: impl IntoValue) {
        self.0.push(Move(dest.into(), src.into()));
    }

    fn unary(&mut self, op: UnaryOp, dest: impl IntoValue, src: impl IntoValue) {
        self.0.push(Unary(op, P32, dest.into(), src.into()));
    }

    /**
     * Apply 32-bit `op` to `src1` and `src2`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn binary(&mut self, op: BinaryOp, dest: impl IntoValue, src1: impl IntoValue, src2: impl IntoValue) {
        self.0.push(Binary(op, P32, TEMP, src1.into(), src2.into()));
        self.move_(dest, TEMP);
    }

    /**
     * Apply 32-bit `op` to `src` and `constant`, writing `dest`.
     * `TEMP` is corrupted.
     */
    fn const_binary(&mut self, op: BinaryOp, dest: impl IntoValue, src: impl IntoValue, constant: i64) {
        assert_ne!(src.into(), TEMP.into());
        self.const_(TEMP, constant);
        self.binary(op, dest, src, TEMP);
    }

    /**
     * Compute the native address corresponding to `addr`.
     */
    fn native_address(&mut self, dest: Register, addr: impl IntoValue) {
        self.0.push(Binary(Add, P64, dest, reg::MEMORY, addr.into()));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn load(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        self.native_address(TEMP, addr);
        self.0.push(Load(dest.into(), (TEMP.into(), Four), MEMORY.into()));
    }

    /**
     * Compute the native address corresponding to `addr`, and store 32 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store(&mut self, src: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(src.into(), (TEMP.into(), Four), MEMORY.into()));
    }

    /**
     * Compute the native address corresponding to `addr`, and load 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn load_byte(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        self.native_address(TEMP, addr);
        self.0.push(Load(dest.into(), (TEMP.into(), One), MEMORY.into()));
    }

    /**
     * Compute the native address corresponding to `addr`, and store 8 bits.
     * `TEMP` is corrupted.
     */
    // TODO: Bounds checking.
    fn store_byte(&mut self, src: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(src.into(), TEMP.into());
        self.native_address(TEMP, addr);
        self.0.push(Store(src.into(), (TEMP.into(), One), MEMORY.into()));
    }

    /**
     * `load()` `dest` from `addr`, then increment `addr`.
     * `TEMP` is corrupted.
     */
    fn pop(&mut self, dest: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(dest.into(), addr.into());
        assert_ne!(dest.into(), TEMP.into());
        self.load(dest, addr);
        self.const_binary(Add, TEMP, addr, cell_bytes(1));
        self.move_(addr, TEMP);
    }

    /**
     * Decrement `addr` by `cell_bytes(1)`, then `store()` `src` at `addr`.
     * `TEMP` is corrupted.
     */
    fn push(&mut self, src: impl IntoValue, addr: impl IntoValue) {
        assert_ne!(src.into(), TEMP.into());
        assert_ne!(src.into(), addr.into());
        self.const_binary(Sub, TEMP, addr, cell_bytes(1));
        self.move_(addr, TEMP);
        self.store(src, TEMP);
    }

    #[allow(dead_code)]
    fn debug(&mut self, x: impl IntoValue) {
        self.0.push(Debug(x.into()));
    }
}

//-----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Machine;

impl code::Machine for Machine {
    type State = State;

    fn num_globals(&self) -> usize {
        NUM_REGISTERS
    }

    fn get_code(&self, state: Self::State) -> Vec<((TestOp, Precision), Vec<Action>, Self::State)> {
        match state {
            State::Root => {vec![
                build(TestOp::Always, |b| {
                    b.move_(S_A, reg::A);
                    b.const_binary(Asr, RA, reg::A, 8);
                    b.move_(reg::A, RA);
                }, State::Dispatch),
            ]},
            State::Next => {vec![
                build(TestOp::Always, |b| {
                    b.pop(reg::A, reg::EP);
                }, State::Root),
            ]},
            State::Pick => {
                let mut pick = Vec::new();
                for u in 0..4 {
                    pick.push(build(TestOp::Eq(STACK_0, u), |b| {
                        b.const_binary(Add, RD, reg::SP, cell_bytes(u as i64 + 1));
                        b.load(RD, RD);
                        b.store(RD, reg::SP);
                    }, State::Root));
                }
                pick
            },
            State::Roll => {
                let mut roll = Vec::new();
                for u in 0..4 {
                    roll.push(build(TestOp::Eq(STACK_0, u as i32), |b| {
                        b.const_binary(Add, RBP, reg::SP, cell_bytes(u));
                        b.load(RB, RBP);
                        for v in 0..u {
                            b.const_binary(Add, RSI, reg::SP, cell_bytes(v));
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
                build(TestOp::Eq(STACK_0, 0), |_| {}, State::Root),
                build(TestOp::Ne(STACK_0, 0), |b| {
                    b.push(STACK_0, reg::SP);
                }, State::Root),
            ]},
            State::Lshift => {vec![
                build(TestOp::Ult(STACK_1, CELL_BITS as i32), |b| {
                    b.binary(Lsl, RD, STACK_0, STACK_1);
                    b.store(RD, reg::SP);
                }, State::Root),
                build(TestOp::Uge(STACK_1, CELL_BITS as i32), |b| {
                    b.const_(RD, 0);
                    b.store(RD, reg::SP);
                }, State::Root),
            ]},
            State::Rshift => {vec![
                build(TestOp::Ult(STACK_1, CELL_BITS as i32), |b| {
                    b.binary(Lsr, RD, STACK_0, STACK_1);
                    b.store(RD, reg::SP);
                }, State::Root),
                build(TestOp::Uge(STACK_1, CELL_BITS as i32), |b| {
                    b.const_(RD, 0);
                    b.store(RD, reg::SP);
                }, State::Root),
            ]},
            State::Branch => {vec![
                build(TestOp::Always, |b| {
                    // Load EP from the cell it points to.
                    b.load(reg::EP, reg::EP); // FIXME: Add check that EP is valid.
                }, State::Next),
            ]},
            State::Branchi => {vec![
                build(TestOp::Always, |b| {
                    b.const_binary(Mul, RD, reg::A, cell_bytes(1));
                    b.binary(Add, reg::EP, reg::EP, RD); // FIXME: Add check that EP is valid.
                }, State::Next),
            ]},
            State::Qbranch => {vec![
                build(TestOp::Eq(STACK_0, 0), |_| {}, State::Branch),
                build(TestOp::Ne(STACK_0, 0), |b| {
                    b.const_binary(Add, reg::EP, reg::EP, cell_bytes(1));
                }, State::Root),
            ]},
            State::Qbranchi => {vec![
                build(TestOp::Eq(STACK_0, 0), |_| {}, State::Branchi),
                build(TestOp::Ne(STACK_0, 0), |_| {}, State::Next),
            ]},
            State::Loop => {vec![
                build(TestOp::Eq(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, reg::EP, reg::EP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, State::Root),
                build(TestOp::Ne(LOOP_FLAG, 0), |_| {}, State::Branch),
            ]},
            State::Loopi => {vec![
                build(TestOp::Eq(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                }, State::Next),
                build(TestOp::Ne(LOOP_FLAG, 0), |_| {}, State::Branchi),
            ]},
            State::Ploopp => {vec![
                build(TestOp::Lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, reg::EP, reg::EP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, State::Root),
                build(TestOp::Ge(LOOP_FLAG, 0), |_| {}, State::Branch),
            ]},
            State::Ploopm => {vec![
                build(TestOp::Lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                    // Add 4 to EP.
                    b.const_binary(Add, reg::EP, reg::EP, cell_bytes(1)); // FIXME: Add check that EP is valid.
                }, State::Root),
                build(TestOp::Ge(LOOP_FLAG, 0), |_| {}, State::Branch),
            ]},
            State::Ploop => {vec![
                build(TestOp::Ge(LOOP_STEP, 0), |b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                }, State::Ploopp),
                build(TestOp::Lt(LOOP_STEP, 0), |b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                }, State::Ploopm),
            ]},
            State::Ploopip => {vec![
                build(TestOp::Lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                }, State::Root),
                build(TestOp::Ge(LOOP_FLAG, 0), |_| {}, State::Branchi),
            ]},
            State::Ploopim => {vec![
                build(TestOp::Lt(LOOP_FLAG, 0), |b| {
                    // Discard the loop index and limit.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                }, State::Root),
                build(TestOp::Ge(LOOP_FLAG, 0), |_| {}, State::Branchi),
            ]},
            State::Ploopi => {vec![
                build(TestOp::Ge(RD.into(), 0), |b| {
                    b.unary(Not, LOOP_NEW, LOOP_NEW);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                }, State::Ploopip),
                build(TestOp::Lt(RD.into(), 0), |b| {
                    b.unary(Not, LOOP_OLD, LOOP_OLD);
                    b.binary(And, LOOP_NEW, LOOP_NEW, LOOP_OLD);
                }, State::Ploopim),
            ]},
            State::Halt => {vec![]},
            State::Dispatch => {vec![
                // NEXT
                build(TestOp::Bits(S_A, 0xff, 0x00), |_| {}, State::Next),

                // DUP
                build(TestOp::Bits(S_A, 0xff, 0x01), |b| {
                    b.load(RD, reg::SP);
                    b.push(RD, reg::SP);
                }, State::Root),

                // DROP
                build(TestOp::Bits(S_A, 0xff, 0x02), |b| {
                    b.const_binary(Add, reg::SP, reg::SP, cell_bytes(1));
                }, State::Root),

                // SWAP
                build(TestOp::Bits(S_A, 0xff, 0x03), |b| {
                    b.pop(RSI, reg::SP);
                    b.load(RB, reg::SP);
                    b.store(RSI, reg::SP);
                    b.push(RB, reg::SP);
                }, State::Root),

                // OVER
                build(TestOp::Bits(S_A, 0xff, 0x04), |b| {
                    b.const_binary(Add, RD, reg::SP, cell_bytes(1));
                    b.load(RB, RD);
                    b.push(RB, reg::SP);
                }, State::Root),

                // ROT
                build(TestOp::Bits(S_A, 0xff, 0x05), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Add, RBP, reg::SP, cell_bytes(1));
                    b.load(RB, RBP);
                    b.store(RD, RBP);
                    b.const_binary(Add, RBP, reg::SP, cell_bytes(2));
                    b.load(RD, RBP);
                    b.store(RB, RBP);
                    b.store(RD, reg::SP);
                }, State::Root),

                // -ROT
                build(TestOp::Bits(S_A, 0xff, 0x06), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Add, RBP, reg::SP, cell_bytes(2));
                    b.load(RB, RBP);
                    b.store(RD, RBP);
                    b.const_binary(Add, RBP, reg::SP, cell_bytes(1));
                    b.load(RD, RBP);
                    b.store(RB, RBP);
                    b.store(RD, reg::SP);
                }, State::Root),

                // TUCK
                build(TestOp::Bits(S_A, 0xff, 0x07), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Add, RBP, reg::SP, cell_bytes(1));
                    b.load(RB, RBP);
                    b.store(RD, RBP);
                    b.store(RB, reg::SP);
                    b.push(RD, reg::SP);
                }, State::Root),

                // NIP
                build(TestOp::Bits(S_A, 0xff, 0x08), |b| {
                    b.pop(RD, reg::SP);
                    b.store(RD, reg::SP);
                }, State::Root),

                // PICK
                build(TestOp::Bits(S_A, 0xff, 0x09), |b| {
                    b.load(STACK_0, reg::SP);
                }, State::Pick),

                // ROLL
                build(TestOp::Bits(S_A, 0xff, 0x0a), |b| {
                    b.pop(STACK_0, reg::SP);
                }, State::Roll),

                // ?DUP
                build(TestOp::Bits(S_A, 0xff, 0x0b), |b| {
                    b.load(STACK_0, reg::SP);
                }, State::Qdup),

                // >R
                build(TestOp::Bits(S_A, 0xff, 0x0c), |b| {
                    b.pop(RD, reg::SP);
                    b.push(RD, reg::RP);
                }, State::Root),

                // R>
                build(TestOp::Bits(S_A, 0xff, 0x0d), |b| {
                    b.pop(RD, reg::RP);
                    b.push(RD, reg::SP);
                }, State::Root),

                // R@
                build(TestOp::Bits(S_A, 0xff, 0x0e), |b| {
                    b.load(RD, reg::RP);
                    b.push(RD, reg::SP);
                }, State::Root),

                // <
                build(TestOp::Bits(S_A, 0xff, 0x0f), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Lt, RD, RSI, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // >
                build(TestOp::Bits(S_A, 0xff, 0x10), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Lt, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // =
                build(TestOp::Bits(S_A, 0xff, 0x11), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Eq, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // <>
                build(TestOp::Bits(S_A, 0xff, 0x12), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Eq, RD, RD, RSI);
                    b.unary(Not, RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 0<
                build(TestOp::Bits(S_A, 0xff, 0x13), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Lt, RD, RD, 0);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 0>
                build(TestOp::Bits(S_A, 0xff, 0x14), |b| {
                    b.load(RD, reg::SP);
                    b.const_(RSI, 0);
                    b.binary(Lt, RD, RSI, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 0=
                build(TestOp::Bits(S_A, 0xff, 0x15), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Eq, RD, RD, 0);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 0<>
                build(TestOp::Bits(S_A, 0xff, 0x16), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Eq, RD, RD, 0);
                    b.unary(Not, RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // U<
                build(TestOp::Bits(S_A, 0xff, 0x17), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Ult, RD, RSI, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // U>
                build(TestOp::Bits(S_A, 0xff, 0x18), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Ult, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 0
                build(TestOp::Bits(S_A, 0xff, 0x19), |b| {
                    b.const_(RSI, 0);
                    b.push(RSI, reg::SP);
                }, State::Root),

                // 1
                build(TestOp::Bits(S_A, 0xff, 0x1a), |b| {
                    b.const_(RSI, 1);
                    b.push(RSI, reg::SP);
                }, State::Root),

                // -1
                build(TestOp::Bits(S_A, 0xff, 0x1b), |b| {
                    b.const_(RSI, -1);
                    b.push(RSI, reg::SP);
                }, State::Root),

                // CELL
                build(TestOp::Bits(S_A, 0xff, 0x1c), |b| {
                    b.const_(RSI, cell_bytes(1));
                    b.push(RSI, reg::SP);
                }, State::Root),

                // -CELL
                build(TestOp::Bits(S_A, 0xff, 0x1d), |b| {
                    b.const_(RSI, (-Wrapping(cell_bytes(1))).0);
                    b.push(RSI, reg::SP);
                }, State::Root),

                // +
                build(TestOp::Bits(S_A, 0xff, 0x1e), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Add, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // -
                build(TestOp::Bits(S_A, 0xff, 0x1f), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Sub, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // >-<
                build(TestOp::Bits(S_A, 0xff, 0x20), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Sub, RD, RSI, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 1+
                build(TestOp::Bits(S_A, 0xff, 0x21), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Add, RD, RD, 1);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 1-
                build(TestOp::Bits(S_A, 0xff, 0x22), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Sub, RD, RD, 1);
                    b.store(RD, reg::SP);
                }, State::Root),

                // CELL+
                build(TestOp::Bits(S_A, 0xff, 0x23), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Add, RD, RD, cell_bytes(1));
                    b.store(RD, reg::SP);
                }, State::Root),

                // CELL-
                build(TestOp::Bits(S_A, 0xff, 0x24), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Sub, RD, RD, cell_bytes(1));
                    b.store(RD, reg::SP);
                }, State::Root),

                // *
                build(TestOp::Bits(S_A, 0xff, 0x25), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Mul, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                /* TODO:
                // /
                build(TestOp::Bits(S_A, 0xff, 0x26), |_| {
                    // TODO
                }, State::Root),

                // MOD
                build(TestOp::Bits(S_A, 0xff, 0x27), |_| {
                    // TODO
                }, State::Root),

                // /MOD
                build(TestOp::Bits(S_A, 0xff, 0x28), |_| {
                    // TODO
                }, State::Root),

                // U/MOD
                build(TestOp::Bits(S_A, 0xff, 0x29), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RA, reg::SP);
                    b.0.push(Division(UnsignedDivMod, P32, RA, RD, RA, RD));
                    b.store(RD, reg::SP);
                    b.push(RA, reg::SP);
                }, State::Root),

                // S/REM
                build(TestOp::Bits(S_A, 0xff, 0x2a), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RA, reg::SP);
                    b.0.push(Division(SignedDivMod, P32, RA, RD, RA, RD));
                    b.store(RD, reg::SP);
                    b.push(RA, reg::SP);
                }, State::Root),
                */

                // 2/
                build(TestOp::Bits(S_A, 0xff, 0x2b), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Asr, RD, RD, 1);
                    b.store(RD, reg::SP);
                }, State::Root),

                // CELLS
                build(TestOp::Bits(S_A, 0xff, 0x2c), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Mul, RD, RD, cell_bytes(1));
                    b.store(RD, reg::SP);
                }, State::Root),

                // ABS
                build(TestOp::Bits(S_A, 0xff, 0x2d), |b| {
                    b.load(RD, reg::SP);
                    b.unary(Abs, RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // NEGATE
                build(TestOp::Bits(S_A, 0xff, 0x2e), |b| {
                    b.load(RD, reg::SP);
                    b.unary(Negate, RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // MAX
                build(TestOp::Bits(S_A, 0xff, 0x2f), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Max, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // MIN
                build(TestOp::Bits(S_A, 0xff, 0x30), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Min, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // INVERT
                build(TestOp::Bits(S_A, 0xff, 0x31), |b| {
                    b.load(RD, reg::SP);
                    b.unary(Not, RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // AND
                build(TestOp::Bits(S_A, 0xff, 0x32), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(And, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // OR
                build(TestOp::Bits(S_A, 0xff, 0x33), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Or, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // XOR
                build(TestOp::Bits(S_A, 0xff, 0x34), |b| {
                    b.pop(RD, reg::SP);
                    b.load(RSI, reg::SP);
                    b.binary(Xor, RD, RD, RSI);
                    b.store(RD, reg::SP);
                }, State::Root),

                // LSHIFT
                build(TestOp::Bits(S_A, 0xff, 0x35), |b| {
                    b.pop(STACK_0, reg::SP);
                    b.load(STACK_1, reg::SP);
                }, State::Lshift),

                // RSHIFT
                build(TestOp::Bits(S_A, 0xff, 0x36), |b| {
                    b.pop(STACK_0, reg::SP);
                    b.load(STACK_1, reg::SP);
                }, State::Rshift),

                // 1LSHIFT
                build(TestOp::Bits(S_A, 0xff, 0x37), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Lsl, RD, RD, 1);
                    b.store(RD, reg::SP);
                }, State::Root),

                // 1RSHIFT
                build(TestOp::Bits(S_A, 0xff, 0x38), |b| {
                    b.load(RD, reg::SP);
                    b.const_binary(Lsr, RD, RD, 1);
                    b.store(RD, reg::SP);
                }, State::Root),

                // @
                build(TestOp::Bits(S_A, 0xff, 0x39), |b| {
                    b.load(RD, reg::SP);
                    b.load(RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // !
                build(TestOp::Bits(S_A, 0xff, 0x3a), |b| {
                    b.pop(RD, reg::SP);
                    b.pop(RB, reg::SP);
                    b.store(RB, RD);
                }, State::Root),

                // C@
                build(TestOp::Bits(S_A, 0xff, 0x3b), |b| {
                    b.load(RD, reg::SP);
                    b.load_byte(RD, RD);
                    b.store(RD, reg::SP);
                }, State::Root),

                // C!
                build(TestOp::Bits(S_A, 0xff, 0x3c), |b| {
                    b.pop(RD, reg::SP);
                    b.pop(RB, reg::SP);
                    b.store_byte(RB, RD);
                }, State::Root),

                // +!
                build(TestOp::Bits(S_A, 0xff, 0x3d), |b| {
                    b.pop(RD, reg::SP);
                    b.pop(RB, reg::SP);
                    b.load(RBP, RD);
                    b.binary(Add, RB, RBP, RB);
                    b.store(RB, RD);
                }, State::Root),

                // SP@
                build(TestOp::Bits(S_A, 0xff, 0x3e), |b| {
                    b.move_(RA, reg::SP);
                    b.push(RA, reg::SP);
                }, State::Root),

                // SP!
                build(TestOp::Bits(S_A, 0xff, 0x3f), |b| {
                    b.load(reg::SP, reg::SP);
                }, State::Root),

                // RP@
                build(TestOp::Bits(S_A, 0xff, 0x40), |b| {
                    b.push(reg::RP, reg::SP);
                }, State::Root),

                // RP!
                build(TestOp::Bits(S_A, 0xff, 0x41), |b| {
                    b.pop(reg::RP, reg::SP);
                }, State::Root),

                // EP@
                build(TestOp::Bits(S_A, 0xff, 0x42), |b| {
                    b.push(reg::EP, reg::SP);
                }, State::Root),

                // S0@
                build(TestOp::Bits(S_A, 0xff, 0x43), |b| {
                    b.push(reg::S0, reg::SP);
                }, State::Root),

                // S0!
                build(TestOp::Bits(S_A, 0xff, 0x44), |b| {
                    b.pop(reg::S0, reg::SP);
                }, State::Root),

                // R0@
                build(TestOp::Bits(S_A, 0xff, 0x45), |b| {
                    b.push(reg::R0, reg::SP);
                }, State::Root),

                // R0!
                build(TestOp::Bits(S_A, 0xff, 0x46), |b| {
                    b.pop(reg::R0, reg::SP);
                }, State::Root),

                // 'THROW@
                build(TestOp::Bits(S_A, 0xff, 0x47), |b| {
                    b.push(reg::THROW, reg::SP);
                }, State::Root),

                // 'THROW!
                build(TestOp::Bits(S_A, 0xff, 0x48), |b| {
                    b.pop(reg::THROW, reg::SP);
                }, State::Root),

                // MEMORY@
                build(TestOp::Bits(S_A, 0xff, 0x49), |b| {
                    b.push(reg::MEMORY, reg::SP);
                }, State::Root),

                // 'BAD@
                build(TestOp::Bits(S_A, 0xff, 0x4a), |b| {
                    b.push(reg::BAD, reg::SP);
                }, State::Root),

                // -ADDRESS@
                build(TestOp::Bits(S_A, 0xff, 0x4b), |b| {
                    b.push(reg::NOT_ADDRESS, reg::SP);
                }, State::Root),

                // BRANCH
                build(TestOp::Bits(S_A, 0xff, 0x4c), |_| {}, State::Branch),

                // BRANCHI
                build(TestOp::Bits(S_A, 0xff, 0x4d), |_| {}, State::Branchi),

                // ?BRANCH
                build(TestOp::Bits(S_A, 0xff, 0x4e), |b| {
                    b.pop(STACK_0, reg::SP);
                }, State::Qbranch),

                // ?BRANCHI
                build(TestOp::Bits(S_A, 0xff, 0x4f), |b| {
                    b.pop(STACK_0, reg::SP);
                }, State::Qbranchi),

                // EXECUTE
                build(TestOp::Bits(S_A, 0xff, 0x50), |b| {
                    b.push(reg::EP, reg::RP);
                    b.pop(reg::EP, reg::SP); // FIXME: Add check that EP is valid.
                }, State::Next),

                // @EXECUTE
                build(TestOp::Bits(S_A, 0xff, 0x51), |b| {
                    b.push(reg::EP, reg::RP);
                    b.pop(RA, reg::SP);
                    b.load(reg::EP, RA); // FIXME: Add check that EP is valid.
                }, State::Next),

                // CALL
                build(TestOp::Bits(S_A, 0xff, 0x52), |b| {
                    b.const_binary(Add, RA, reg::EP, cell_bytes(1));
                    b.push(RA, reg::RP);
                }, State::Branch),

                // CALLI
                build(TestOp::Bits(S_A, 0xff, 0x53), |b| {
                    b.push(reg::EP, reg::RP);
                }, State::Branchi),

                // EXIT
                build(TestOp::Bits(S_A, 0xff, 0x54), |b| {
                    b.pop(reg::EP, reg::RP); // FIXME: Add check that EP is valid.
                }, State::Next),

                // (DO)
                build(TestOp::Bits(S_A, 0xff, 0x55), |b| {
                    // Pop two items from SP.
                    b.pop(RSI, reg::SP);
                    b.pop(RB, reg::SP);
                    // Push two items to RP.
                    b.push(RB, reg::RP);
                    b.push(RSI, reg::RP);
                }, State::Root),

                // (LOOP)
                build(TestOp::Bits(S_A, 0xff, 0x56), |b| {
                    // Load the index and limit from RP.
                    b.pop(RB, reg::RP);
                    b.load(RSI, reg::RP);
                    // Update the index.
                    b.const_binary(Add, RB, RB, 1);
                    b.push(RB, reg::RP);
                    b.binary(Sub, LOOP_FLAG, RB, RSI);
                }, State::Loop),

                // (LOOP)I
                build(TestOp::Bits(S_A, 0xff, 0x57), |b| {
                    // Load the index and limit from RP.
                    b.pop(RB, reg::RP);
                    b.load(RSI, reg::RP);
                    // Update the index.
                    b.const_binary(Add, RB, RB, 1);
                    b.push(RB, reg::RP);
                    b.binary(Sub, LOOP_FLAG, RB, RSI);
                }, State::Loopi),

                // (+LOOP)
                build(TestOp::Bits(S_A, 0xff, 0x58), |b| {
                    // Pop the step from SP.
                    b.pop(LOOP_STEP, reg::SP);
                    // Load the index and limit from RP.
                    b.pop(RB, reg::RP);
                    b.load(RSI, reg::RP);
                    // Update the index.
                    b.binary(Add, RBP, RB, LOOP_STEP);
                    b.push(RBP, reg::RP);
                    // Compute the differences between old and new indexes and limit.
                    b.binary(Sub, LOOP_OLD, RB, RSI);
                    b.binary(Sub, LOOP_NEW, RBP, RSI);
                }, State::Ploop),

                // (+LOOP)I
                build(TestOp::Bits(S_A, 0xff, 0x59), |b| {
                    // Pop the step from SP.
                    b.pop(RD, reg::SP);
                    // Load the index and limit from RP.
                    b.pop(RB, reg::RP);
                    b.load(RSI, reg::RP);
                    // Update the index.
                    b.binary(Add, RBP, RB, RD);
                    b.push(RBP, reg::RP);
                    // Compute the differences between old and new indexes and limit.
                    b.binary(Sub, LOOP_OLD, RB, RSI);
                    b.binary(Sub, LOOP_NEW, RBP, RSI);
                }, State::Ploopi),

                // UNLOOP
                build(TestOp::Bits(S_A, 0xff, 0x5a), |b| {
                    // Discard two items from RP.
                    b.const_binary(Add, reg::RP, reg::RP, cell_bytes(2));
                }, State::Root),

                // J
                build(TestOp::Bits(S_A, 0xff, 0x5b), |b| {
                    // Push the third item of RP to SP.
                    b.const_binary(Add, RA, reg::RP, cell_bytes(2));
                    b.load(RSI, RA);
                    b.push(RSI, reg::SP);
                }, State::Root),

                // (LITERAL)
                build(TestOp::Bits(S_A, 0xff, 0x5c), |b| {
                    // Load RD from cell pointed to by EP, and add 4 to EP.
                    b.pop(RD, reg::EP); // FIXME: Add check that EP is now valid.
                    b.push(RD, reg::SP);
                }, State::Root),

                // (LITERAL)I
                build(TestOp::Bits(S_A, 0xff, 0x5d), |b| {
                    b.push(reg::A, reg::SP);
                }, State::Next),

                // THROW
                build(TestOp::Bits(S_A, 0xff, 0x5e), |b| {
                    b.move_(reg::BAD, reg::EP);
                    b.load(reg::EP, reg::THROW); // FIXME: Add check that EP is valid.
                }, State::Next),

                // HALT
                build(TestOp::Bits(S_A, 0xff, 0x5f), |_| {}, State::Halt),
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
    use super::*;

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

    use crate::{jit};

    /** The size of the Beetle memory, in cells. */
    const MEMORY_CELLS: usize = 1 << 20;
    /** The size of the Beetle data stack, in cells. */
    const DATA_CELLS: usize = 1 << 18;
    /** The size of the Beetle return stack, in cells. */
    const RETURN_CELLS: usize = 1 << 18;

    pub struct VM {
        /** The compiled code, registers, and other compiler state. */
        jit: jit::Jit<Machine>,
        /** The Beetle memory. */
        memory: Vec<u32>,
        /** The amount of unallocated memory, in cells. */
        free_cells: u32,
        /** The address of a HALT instruction. */
        halt_addr: u32,
    }

    impl VM {
        /**
         * Constructs a Beetle virtual machine with the specified parameters.
         *
         * The memory is `memory_cells` cells. The data stack occupies the last
         * `data_cells` cells of the memory, and the return stack occupies
         * the last `return_cells` cells before that. The cells before that
         * are free for the program's use.
         */
        pub fn new(
            memory_cells: usize,
            data_cells: usize,
            return_cells: usize,
        ) -> Self {
            assert!(memory_cells <= u32::MAX as usize);
            assert!(data_cells <= u32::MAX as usize);
            assert!(return_cells <= u32::MAX as usize);
            let mut vm = VM {
                jit: jit::Jit::new(Machine, jit::tests::CODE_SIZE),
                memory: (0..memory_cells).map(|_| 0).collect(),
                free_cells: memory_cells as u32,
                halt_addr: 0,
            };
            // Initialize the memory.
            *vm.jit.slot(reg::MEMORY) = vm.memory.as_mut_ptr() as u64;
            // Allocate the data stack.
            let s_base = vm.allocate(data_cells as u32);
            let sp = s_base + cell_bytes(data_cells as i64) as u32;
            vm.set(reg::S0, sp);
            vm.set(reg::SP, sp);
            // Allocate the return stack.
            let r_base = vm.allocate(return_cells as u32);
            let rp = r_base + cell_bytes(return_cells as i64) as u32;
            vm.set(reg::R0, rp);
            vm.set(reg::RP, rp);
            // Allocate a word to hold a HALT instruction.
            vm.halt_addr = vm.allocate(1);
            vm.store(vm.halt_addr, 0x5F);
            vm
        }

        /** Read a register. */
        pub fn get(&mut self, global: Value) -> u32 {
            *self.jit.slot(global) as u32
        }

        /** Write a register. */
        pub fn set(&mut self, global: Value, value: u32) {
            *self.jit.slot(global) = value as u64
        }

        /**
         * Allocate `cells` cells and return a Beetle pointer to them.
         * Allocation starts at the top of memory and is permanent.
         */
        pub fn allocate(&mut self, cells: u32) -> u32 {
            assert!(cells <= self.free_cells);
            self.free_cells -= cells;
            cell_bytes(self.free_cells as i64) as u32
        }

        /**
         * Load `object` at address zero, i.e. in the unallocated memory.
         */
        pub fn load_object(&mut self, object: &[u32]) {
            assert!(object.len() <= self.free_cells as usize);
            for (i, &cell) in object.iter().enumerate() {
                self.memory[i] = cell;
            }
        }

        /** Return the value of the word at address `addr`. */
        pub fn load(&mut self, addr: u32) -> u32 {
            assert_eq!(addr & 0x3, 0);
            self.memory[(addr >> 2) as usize]
        }

        /** Set the word at address `addr` to `value`. */
        pub fn store(&mut self, addr: u32, value: u32) {
            assert_eq!(addr & 0x3, 0);
            self.memory[(addr >> 2) as usize] = value;
        }

        /** Push `item` onto the data stack. */
        pub fn push(&mut self, item: u32) {
            let mut sp = self.get(reg::SP);
            sp -= cell_bytes(1) as u32;
            self.set(reg::SP, sp);
            self.store(sp, item);
        }

        /** Pop an item from the data stack. */
        pub fn pop(&mut self) -> u32 {
            let mut sp = self.get(reg::SP);
            let item = self.load(sp);
            sp += cell_bytes(1) as u32;
            self.set(reg::SP, sp);
            item
        }

        /** Push `item` onto the return stack. */
        pub fn rpush(&mut self, item: u32) {
            let mut rp = self.get(reg::RP);
            rp -= cell_bytes(1) as u32;
            self.set(reg::RP, rp);
            self.store(rp, item);
        }

        /** Pop an item from the return stack. */
        pub fn rpop(&mut self) -> u32 {
            let mut rp = self.get(reg::RP);
            let item = self.load(rp);
            rp += cell_bytes(1) as u32;
            self.set(reg::RP, rp);
            item
        }

        /** Run the code at address `ep`. */
        pub fn run(mut self, ep: u32) -> Self {
            assert!(Self::is_aligned(ep));
            self.set(reg::EP, ep);
            let (jit, state) = self.jit.execute(State::Root);
	    assert_eq!(state, State::Halt);
            self.jit = jit;
            self
        }

        /** Indicate whether an address is cell-aligned. */
        pub fn is_aligned(addr: u32) -> bool {
            addr & 0x3 == 0
        }
    }

    #[test]
    pub fn ackermann() {
        let mut vm = VM::new(MEMORY_CELLS, DATA_CELLS, RETURN_CELLS);
        vm.load_object(ackermann_object().as_ref());
        vm.push(3);
        vm.push(5);
        vm.rpush(vm.halt_addr);
        vm = vm.run(0);
        let result = vm.pop();
        assert_eq!(vm.get(reg::S0), vm.get(reg::SP));
        assert_eq!(vm.get(reg::R0), vm.get(reg::RP));
        assert_eq!(result, 253);
    }
}
