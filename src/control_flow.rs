//! Data structures for representing the control-flow graph of an interpreter.

use std::fmt::{Debug};
use std::hash::{Hash};

use super::{code};

/// Use as a memory address.
pub trait Address: Debug + Clone + Hash + Eq {
    fn can_alias(&self, other: &Self) -> bool;
}

pub trait Machine: Debug {
    type State: Debug + Clone + Hash + Eq;
    type Address: Address;
    fn get_code(state: Self::State) ->
        Vec<(
            code::TestOp,
            Vec<code::Action<Self::Address>>,
            Self::State
        )>;
}