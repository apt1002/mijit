use std::num::{Wrapping};

use super::{control_flow};
pub use super::x86_64::{Register as R};

pub enum TestOp {
    Bit(Wrapping<u32>, Wrapping<u32>),
    Lt(Wrapping<u32>),
    Ult(Wrapping<u32>),
    Eq(Wrapping<u32>),
}

// TODO: Support tests with more than one register operand.
pub struct Test {
    pub register: R,
    pub test_op: TestOp,
    pub must_be: bool, // Desired outcome of `test_op`.
}

pub enum UnaryOp {
    Abs,
    Negate,
    Max,
    Min,
    Not,
}

pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Lsl,
    Lsr,
    Asr,
    And,
    Or,
    Xor,
    Lt,
    Ult,
    Eq,
}

pub enum DivisionOp {
    SignedDivMod,
    UnsignedDivMod,
}

pub enum Width {
    One,
    Two,
    Four,
}

pub enum Action<A: control_flow::Address> {
    Constant(R, Wrapping<u32>),
    Move(R, R),
    Unary(UnaryOp, R, R),
    Binary(BinaryOp, R, R, R),
    Division(DivisionOp, R, R, R, R),
    Load(R, A),
    Store(R, A),
    LoadNarrow(Width, R, A),
    StoreNarrow(Width, R, A),
    Push(R),
    Pop(R),
}

pub struct Code<A: control_flow::Address> {
    pub native_address: *mut u8,
    pub condition: Test,
    pub actions: Vec<Action<A>>,
}
