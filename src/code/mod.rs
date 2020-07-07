/*!
 * Mijit's instruction set. This instruction set is used to define virtual
 * machines, and it is also used to remember what code Mijit has generated.
 */

pub use super::x86_64::{Register as R};

pub mod control_flow;
pub use control_flow::{Machine, Address};

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

/** Unary arithmetic operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Abs,
    Negate,
    Not,
}

/** Binary arithmetic operations. */
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
    Max,
    Min,
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
