//! Data structures for representing the control-flow graph of an interpreter.

use std::fmt::{Debug};
use std::hash::{Hash};

use super::{code};

/// Use as a memory address.
pub trait Address: Debug + Clone + Hash + Eq {
    fn can_alias(&self, other: &Self) -> bool;
}

pub enum Action<A: Address> {
    Constant(u32),
    Unary(code::UnaryOp),
    Binary(code::BinaryOp),
    Division(code::DivisionOp),
    Push(A),
    Pop(A),
}

pub struct State<A: Address> {
    pub actions: Vec<Action<A>>,
    pub condition: code::Test,
    pub if_true: usize,
    pub if_false: usize,
}

pub struct Machine<A: Address> {
    pub states: Vec<State<A>>,
}
