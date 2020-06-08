use std::num::{Wrapping};

use super::{control_flow};
pub use super::x86_64::{Register as R};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TestOp {
    Bit(Wrapping<u32>, Wrapping<u32>),
    Lt(Wrapping<u32>),
    Ge(Wrapping<u32>),
    Ult(Wrapping<u32>),
    Uge(Wrapping<u32>),
    Eq(Wrapping<u32>),
    Ne(Wrapping<u32>),
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
