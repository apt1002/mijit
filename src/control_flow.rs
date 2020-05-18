//! Data structures for representing the control-flow graph of an interpreter.

use std::fmt::{Debug};
use std::hash::{Hash};

/// Use as a memory address.
pub trait Address: Debug + Clone + Hash + Eq {
    fn can_alias(&self, other: &Self) -> bool;
}

pub trait Register: Debug + Clone + Hash + Eq {}

pub enum ArithmeticOp {
    Add,
    Sub,
    Mul,
    Lsl,
    Lsr,
    Asr,
    
}

pub enum Action<R: Register> {
    Constant(R, u32),
    Arithmetic(ArithmeticOp, R, R, R),
    Load(R, R),
    Store(R, R),
}

pub enum Test<R> {
    Bit(R, u8),
    Lt(R, R),
    Ult(R, R),
    Eq(R, R),
}

pub struct State<R: Register> {
    pub actions: Vec<Action<R>>,
    pub condition: Test<R>,
    pub if_true: usize,
    pub if_false: usize,
}

pub struct Machine<R: Register> {
    pub states: Vec<State<R>>,
}
