/*!
 * Mijit's instruction set. This instruction set is used to define virtual
 * machines, and it is also used to remember what code Mijit has generated.
 *
 * A virtual machine's control flow is restricted to a finite state machine,
 * defined by implementing trait [`Machine`]. All the other instructions are
 * branch-free. More complex control flow can be achieved by driving the finite
 * state machine using values loaded from memory.
 *
 * A virtual machine's storage consists of a number of `Variable`s, some of
 * which are global, meaning that their values are preserved when a trap
 * occurs. More complex data structures can be achieved by loading and storing
 * values in memory.
 *
 * Arithmetic operations are 32-bit or 64-bit. 32-bit operations set the upper
 * 32 bits of the destination register to zero.
 *
 * Booleans results are returned as `0` or `-1`.
 */

use std::fmt::{Debug};
use std::hash::{Hash};

mod variable;
pub use variable::{Register, REGISTERS, Global, Slot, Variable, IntoVariable};

mod enums;
pub use enums::{Precision, UnaryOp, BinaryOp, Width, AliasMask};

mod action;
pub use action::{Action, debug_word};

mod switch;
pub use switch::{Case, Switch};

mod ebb;
pub use ebb::{EBB, Ending};

//-----------------------------------------------------------------------------

/**
 * Represents the convention by which code passes values to a label. The
 * concept is similar to a calling convention, but it's for a jump, not a call.
 *
 * This is a place-holder. Possible future uses:
 *  - Knowledge about values, e.g. minimum and maximum possible value, and
 *    which bits are known to be set or clear.
 *  - Knowledge about possible common sub-expressions, e.g. knowing that some
 *    value is the difference of two other values.
 *  - Knowledge about the cache state, e.g. that some value is the value of
 *    some memory location, and whether it needs to be stored.
 */
#[derive(Debug, Clone)]
pub struct Convention {
    /** The values that are live on entry. */
    pub live_values: Box<[Variable]>,
    /** The number of spill [`Slot`]s used by the `Convention`. */
    pub slots_used: usize,
}

/**
 * Returns a [`Convention`] with no [`Slot`]s, no live [`Register`]s, and the
 * specified number of [`Global`]s.
 */
pub fn empty_convention(num_globals: usize) -> Convention {
    Convention {
        live_values: (0..num_globals).map(|g| Variable::Global(Global(g))).collect(),
        slots_used: 0,
    }
}

/** Code to be run on entry and exit from a `Machine`. */
#[derive(Debug, Clone)]
pub struct Marshal {
    /** Code to be run on entry, starting with only [`Global`]s live. */
    pub prologue: Box<[Action]>,
    /** The [`Convention`] after `prologue` and before `epilogue`. */
    pub convention: Convention,
    /** Code to be run on exit, ending with only [`Global`]s live. */
    pub epilogue: Box<[Action]>,
}

//-----------------------------------------------------------------------------

/**
 * A specification of a virtual machine.
 */
pub trait Machine: Debug {
    /** A state of the finite state machine. */
    type State: Debug + Clone + Hash + Eq;

    /** A reason for exiting the finite state machine. */
    type Trap: Debug + Clone + Hash + Eq;

    /** The number of [`Global`]s used by this Machine. */
    fn num_globals(&self) -> usize;

    /**
     * Returns a [`Marshal`] that describes how to enter and exit this
     * `Machine` in `state`.
     *
     * Mijit requires the ability to interrupt the virtual machine in any
     * `State`. Interrupts are used for various purposes, including:
     *  - to suspend execution of the virtual machine in order to compile
     *    faster code.
     *  - for debugging.
     */
    fn marshal(&self, state: Self::State) -> Marshal;

    /**
     * Defines the transitions of the finite state machine.
     *  - state - the source State.
     * Returns a [`Case`] for each transition from `state`.
     */
    fn code(&self, state: Self::State) -> Switch<Case<Result<Self::State, Self::Trap>>>;

    /** Returns some States from which all others are reachable. */
    fn initial_states(&self) -> Vec<Self::State>;
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    pub use action::tests::{Emulator};
}
