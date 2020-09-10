/*!
 * Mijit's instruction set. This instruction set is used to define virtual
 * machines, and it is also used to remember what code Mijit has generated.
 *
 * A virtual machine's control flow is restricted to a finite state machine,
 * defined by implementing trait [`Machine`]. All the other instructions are
 * branch-free. More complex control flow can be achieved by driving the finite
 * state machine using values loaded from memory.
 *
 * A virtual machine's storage is restricted to a finite number of global
 * variables, again defined by implementing trait [`Machine`]. More complex
 * data structures can be achieved by loading and storing values in memory.
 *
 * Arithmetic operations are 32-bit or 64-bit. 32-bit operations set the upper
 * 32 bits of the destination register to zero.
 *
 * Booleans results are returned as `0` or `-1`.
 */

use std::fmt::{Debug};
use std::hash::{Hash};

pub use super::x86_64::{Register as R, Precision};

pub mod clock;

/** Guard conditions used to define control flow. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TestOp {
    // TODO: These constants should probably be 64-bit.
    Bits(R, i32, i32),
    Lt(R, i32),
    Ge(R, i32),
    Ult(R, i32),
    Uge(R, i32),
    Eq(R, i32),
    Ne(R, i32),
    Always,
}

/** Unary arithmetic operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum UnaryOp {
    Abs,
    Negate,
    Not,
    // TODO: Uxt, Sxt (#12).
}

/** Binary arithmetic operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
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

/** Division operations. */
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum DivisionOp {
    SignedDivMod,
    UnsignedDivMod,
}

/** The number of bytes transferred by a memory access. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(u8)]
pub enum Width {
    One = 0,
    Two = 1,
    Four = 2,
    Eight = 3,
}

/**
 * An imperative instruction.
 * The destination register (where applicable) is on the left.
 * M is the type of memory aliasing classes.
 * G is the type of global variable names.
 */
#[derive(Debug, Clone)]
pub enum Action<M, G> {
    Constant(Precision, R, i64),
    Move(R, R),
    Unary(UnaryOp, Precision, R, R),
    Binary(BinaryOp, Precision, R, R, R),
    Division(DivisionOp, Precision, R, R, R, R),
    LoadGlobal(R, G),
    StoreGlobal(R, G),
    Load(R, (R, Width), M),
    Store(R, (R, Width), M),
    Push(R),
    Pop(R),
    Debug(R),
}

/** Test whether memories overlap. */
// TODO: Replace with a bitmask.
// TODO: Actually use this.
pub trait Alias: Debug + Clone + Hash + Eq {
    /**
     * Tests whether an address in `self` and an address in `other` might refer
     * to the same storage location. More precisely, tests whether the value
     * read from one of the addresses can be affected by a write to the other.
     *
     * The relation:
     *  - must be symmetric. `m.can_alias(&n)` must equal `n.can_alias(&m)`.
     *  - must be reflexive if the memory is mutable. If all writes to an
     *    address in `m` precede all reads from the same address, then
     *    `m.can_alias(&m)` can be `false`, otherwise it must be `true`.
     *  - need not be transitive. It is possible that `m.can_alias(&n1)` and
     *    `m.can_alias(&n2)` but not `n1.can_alias(&n2)`.
     *
     * An implementation of `can_alias()` that always returns `true` is
     * allowed, but it is unhelpful. The purpose of this method is to enable
     * the following transformations, which are invalid if `m.can_alias(&n)`:
     *  - Store, load:
     *     - Before: store(n); load(m)
     *     - After: load(m); store(n)
     *  - Load, store:
     *     - Before: load(m); store(n)
     *     - After: store(n); load(m)
     *  - Store, store:
     *     - Before: store(n); store(m)
     *     - After: store(m)
     *
     * The default implementation returns `*self == *other`.
     */
    fn can_alias(&self, other: &Self) -> bool {
        *self == *other
    }
}

pub trait Machine: Debug {
    /** A state of the finite state machine. */
    type State: Debug + Clone + Hash + Eq;

    /** A discrete VM storage location, such as a register. */
    type Global: Debug + Clone + Hash + Eq;

    /** A VM storage location with an address. */
    type Memory: Alias;

    /**
     * Defines the transitions of the finite state machine.
     *  - state - the source State.
     * Returns a (condition, actions, new_state) for each transition from
     * `state`:
     *  - condition - when to use the transition. Mijit selects the first
     *    transition with a true condition.
     *  - actions - code to execute when the transition is selected.
     *  - new_state - the destination State.
     */
    fn get_code(&self, state: Self::State) ->
        Vec<(
            (TestOp, Precision),
            Vec<Action<Self::Memory, Self::Global>>,
            Self::State,
        )>;

    /** Returns some States from which all others are reachable. */
    fn initial_states(&self) -> Vec<Self::State>;
}
