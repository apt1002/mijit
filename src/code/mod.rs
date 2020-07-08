/*!
 * Mijit's instruction set. This instruction set is used to define virtual
 * machines, and it is also used to remember what code Mijit has generated.
 *
 * Control flow is restricted to a finite state machine, defined by
 * implementing trait Machine. All the other instructions are branch-free.
 *
 * Arithmetic operations are all 32-bit (for now). The upper 32 bits of the
 * destination register will be set to zero.
 *
 * Booleans results are returned as `0` or `-1`.
 */

pub use super::x86_64::{Register as R};

pub mod control_flow;
pub use control_flow::{Machine, Address};

pub mod clock;

/** Guard conditions used to define control flow. */
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
    Max, // TODO: Unsigned too?
    Min, // TODO: Unsigned too?
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DivisionOp {
    SignedDivMod,
    UnsignedDivMod,
}

/** Used to specify how many bytes to load or store. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Width {
    One,
    Two,
    Four,
}

/**
 * An imperative instruction.
 * The destination register (where applicable) is on the left.
 */
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
