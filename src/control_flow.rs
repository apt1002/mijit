//! Data structures for representing the control-flow graph of an interpreter.

use std::fmt::{Debug};
use std::hash::{Hash};

use super::{code};

/// Use as a memory address.
pub trait Address: Debug + Clone + Hash + Eq {
    fn can_alias(&self, other: &Self) -> bool;
}

pub struct Test {
    pub condition: code::TestOp,
    pub if_true: usize,
}

pub struct State<A: Address> {
    pub actions: Vec<code::Action<A>>,
    pub regisrer: code::R,
    pub tests: Vec<Test>,
}

pub struct Machine<A: Address> {
    pub states: Vec<State<A>>,
}
