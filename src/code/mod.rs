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
pub use variable::{Register, REGISTERS, Global, Slot, Variable, IntoVariable, FAST_VARIABLES};

mod enums;
pub use enums::{Precision, UnaryOp, BinaryOp, Width, AliasMask};

mod action;
pub use action::{Action, debug_word};

mod switch;
pub use switch::{Case, Switch};

// Not currently used. Planned for #11.
pub mod clock;

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
    pub live_values: Vec<Variable>,
    /** The number of spill [`Slot`]s used by the `Convention`. */
    pub slots_used: usize,
}

//-----------------------------------------------------------------------------

pub trait Machine: Debug {
    /** A state of the finite state machine. */
    type State: Debug + Clone + Hash + Eq;

    /** A reason for exiting the finite state machine. */
    type Trap: Debug + Clone + Hash + Eq;

    /** The number of [`Global`]s used by this Machine. */
    fn num_globals(&self) -> usize;

    /**
     * The number of [`Slot`]s that exist on entry and exit from every
     * [`State`].
     */
    fn num_slots(&self) -> usize;

    /**
     * Returns a bitmask indicating which [`Variable`]s are live in `state`.
     *
     * The bits correspond to members of [`FAST_VARIABLES`].
     */
    fn liveness_mask(&self, state: Self::State) -> u64;

    /**
     * Returns code to marshal data from the [`Global`]s to the live values.
     * It is not passed anything on entry. On exit it must have initialised
     * all [`Variable`]s that are live in any [`State`].
     */
    fn prologue(&self) -> Vec<Action>;

    /**
     * Returns code to marshal data from the live values back to the
     * [`Global`]s.
     *
     * On entry, it gets all [`Variable`]s that are live in any [`State`];
     * those that are dead are set to a dummy value (`0xdeaddeaddeaddead`).
     * On exit only the `Global`s are live.
     */
    fn epilogue(&self) -> Vec<Action>;

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
