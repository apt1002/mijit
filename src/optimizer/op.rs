use super::code::{Precision, UnaryOp, BinaryOp, Width, AliasMask};

/** Compactly represents a kind of [`Action`]. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Op {
    Convention,
    Constant(i64),
    Unary(Precision, UnaryOp),
    Binary(Precision, BinaryOp),
    Load(Width, AliasMask),
    Store(Width, AliasMask),
    Push,
    Pop,
    Debug,
}
