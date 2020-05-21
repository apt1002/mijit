use super::{control_flow};
use super::x86_64::{Register as R};

pub enum TestOp {
    Bit(u32, u32),
    Lt(u32),
    Ult(u32),
    Eq(u32),
}

// TODO: Support tests with more than one register operand.
pub struct Test {
    pub register: R,
    pub test_op: TestOp,
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

pub enum Action<A: control_flow::Address> {
    Constant(R, u32),
    Unary(UnaryOp, R, R),
    Binary(BinaryOp, R, R, R),
    Division(DivisionOp, R, R, R, R),
    Load(R, A),
    Store(R, A),
    Push(R),
    Pop(R),
}

pub struct Code<A: control_flow::Address> {
    pub native_address: *mut u8,
    pub condition: Test,
    pub actions: Vec<Action<A>>,
}
