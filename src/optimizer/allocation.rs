use std::collections::{HashMap};

use crate::util::{RcEq};
use super::super::jit::lowerer::{ALLOCATABLE_REGISTERS};
use super::code::{Action, Value, Register};
use super::dataflow::{Node, Op};

/**
 * Represents the state of the algorithm that flattens the dataflow graph
 * (of Nodes) into a list of [`code::Action`]s.
 */
pub struct Allocation {
    /** The number of spill slots. */
    slots_used: usize,
    /** The Actions so far. */
    pub actions: Vec<Action>, // TODO: Make private.
    /** The location of each Node's result. */
    values: HashMap<RcEq<Node>, Value>,
    /** Map from logical to physical registers. */
    logical_to_physical: [Register; ALLOCATABLE_REGISTERS.len()],
}

impl Allocation {
    pub fn new(logical_to_physical: [Register; ALLOCATABLE_REGISTERS.len()]) -> Self {
        Allocation {
            slots_used: 0,
            actions: Vec::new(),
            values: HashMap::new(),
            logical_to_physical: logical_to_physical,
        }
    }

    /**
     * The Value allocated to hold the result of `node`.
     */
    pub fn lookup(&self, node: &RcEq<Node>) -> Value {
        *self.values.get(node).expect("Unknown Node")
    }

    /**
     * Allocate a destination Value for the result of `node`. If `register` is
     * provided, it is the index of a logical register, and the corresponding
     * physical register will be used. Otherwise, a fresh spill Slot will be
     * allocated.
     *  - node - the Node for which to allocate a destination Value.
     *  - register - the logical register to use, if any.
     */
    fn choose_destination(&mut self, node: RcEq<Node>, register: Option<usize>) -> Value {
        let dest = match register {
            Some(index) => {
                Value::Register(self.logical_to_physical[index])
            },
            None => {
                let index = self.slots_used;
                self.slots_used += 1;
                Value::Slot(index)
            },
        };
        if let Some(_old) = self.values.insert(node, dest) { panic!("Node used twice"); }
        dest
    }

    /**
     * Append `node` to this Allocation, and decide where to store its results.
     * Returns `(dest, src)`.
     *  - node - an Input Node.
     *  - register - the logical register number, or None if the result
     *    should be spilled.
     */
    pub fn input(&mut self, node: RcEq<Node>, register: Option<usize>) -> (Value, Value) {
        let dest = self.choose_destination(node.clone(), register);
        let src = match node.op {
            Op::Input(src) => src,
            _ => panic!("Not an Input"),
        };
        (dest, src)
    }

    /**
     * Append `node` to this Allocation, and decide where to store its results.
     *  - node - a non-Input Node.
     *  - register - the logical register number, or None if the result
     *    should be spilled.
     */
    pub fn node(&mut self, node: RcEq<Node>, register: Option<usize>) {
        let dest = self.choose_destination(node.clone(), register);
        match node.op {
            Op::Input(_) => {
                panic!("Inputs should not be in the Schedule");
            },
            Op::Constant(prec, value) => {
                self.actions.push(Action::Constant(prec, dest, value));
            },
            Op::Unary(op, prec, ref src) => {
                let src = self.lookup(src);
                self.actions.push(Action::Unary(op, prec, dest, src));
            },
            Op::Binary(op, prec, ref src1, ref src2) => {
                let src1 = self.lookup(src1);
                let src2 = self.lookup(src2);
                self.actions.push(Action::Binary(op, prec, dest, src1, src2));
            },
            Op::Load((width, ref addr), _, alias_mask) => {
                let addr = self.lookup(addr);
                self.actions.push(Action::Load(dest, (addr, width), alias_mask));
            },
            Op::Store((width, ref addr), ref src, _, alias_mask) => {
                let addr = self.lookup(addr);
                let src = self.lookup(src);
                self.actions.push(Action::Store(src, (addr, width), alias_mask));
            },
            Op::Push(ref src, _) => {
                let src = self.lookup(src);
                self.actions.push(Action::Push(src));
            },
            Op::Pop(_) => {
                self.actions.push(Action::Pop(dest));
            },
            Op::Debug(ref src, _) => {
                let src = self.lookup(src);
                self.actions.push(Action::Debug(src));
            },
        }
        self.values.insert(node, dest);
    }
}
