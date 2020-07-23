//! Data structures for representing the control-flow graph of an interpreter.

use std::fmt::{Debug};
use std::hash::{Hash};

use super::{TestOp, Action};

/// Test whether memories overlap.
pub trait Alias: Debug + Clone + Hash + Eq {
    /**
     * Tests whether an address in `self` and an address in `other` might refer
     * to the same storage location. Must be symmetric. 
     *
     * The purpose of this method is to enable the following transformations,
     * which are invalid if `self.can_alias(other)`:
     *  1. Store before load:
     *      - Before: store(other); load(self)
     *      - After: load(self); store(other)
     *  2. Store, store:
     *      - Before: store(other); store(self)
     *      - After: store(self)
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
            TestOp,
            Vec<Action<Self::Memory, Self::Global>>,
            Self::State
        )>;

    /** Returns some States from which all others are reachable. */
    fn initial_states(&self) -> Vec<Self::State>;
}
