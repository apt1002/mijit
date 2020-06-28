use super::{control_flow};
pub use super::x86_64::{Register as R};

pub mod clock;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TestOp {
    Bits(R, u32, u32),
    Lt(R, u32),
    Ge(R, u32),
    Ult(R, u32),
    Uge(R, u32),
    Eq(R, u32),
    Ne(R, u32),
    Always,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Abs,
    Negate,
    Max,
    Min,
    Not,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DivisionOp {
    SignedDivMod,
    UnsignedDivMod,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Width {
    One,
    Two,
    Four,
}

#[derive(Debug, Clone)]
pub enum Action<A: control_flow::Address> {
    Constant(R, u32),
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
