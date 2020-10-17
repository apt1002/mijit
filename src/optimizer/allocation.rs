use std::collections::{HashMap};
use std::collections::hash_map::{Entry};

use crate::util::{RcEq};
use super::super::jit::{Convention};
use super::super::jit::lowerer::{ALLOCATABLE_REGISTERS, TEMP_VALUE};
use super::code::{Action, Value, Register};
use super::dataflow::{Node, Op, Simulation};
use super::schedule::{Schedule, LATE};
use super::moves::{moves};

/**
 * Represents the state of the algorithm that flattens the dataflow graph
 * (of Nodes) into a list of [`code::Action`]s.
 */
pub struct Allocation {
    /** The number of spill slots. */
    slots_used: usize,
    /** The Actions so far. */
    actions: Vec<Action>,
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

    pub fn choose_destination(&mut self, logical_reg: Option<usize>) -> Value {
        match logical_reg {
            Some(index) => {
                Value::Register(self.logical_to_physical[index])
            },
            None => {
                let index = self.slots_used;
                self.slots_used += 1;
                Value::Slot(index)
            },
        }
    }

    /**
     * Append `node` to this Allocation, and decide where to store its results.
     *  - register - the logical register number, or None if the result
     *    should be spilled.
     */
    pub fn node(&mut self, node: RcEq<Node>, register: Option<usize>) {
        let dest = self.choose_destination(register);
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


pub fn optimize(
    _before: Convention,
    actions: Vec<Action>,
    after: Convention,
) -> Vec<Action> {
    // `before` is currently unused. We plan to use it in two places:
    // - In 1, to assert that we don't read values unless they are live.
    // - In 3, to choose a logical-to-physical register mapping to avoid moves.
    // 1. Simulation.
    let mut simulation = Simulation::new();
    for action in actions {
        simulation.action(action);
    }
    // 2. Schedule.
    let roots: Vec<_> = after.live_values.iter().map(|&value| {
        (simulation.lookup(value), LATE)
    }).collect();
    let schedule = Schedule::new(roots);
    // 3. Match `before`.
    // TODO.
    // 4. Allocation.
    let mut allocation = Allocation::new(ALLOCATABLE_REGISTERS /* TODO: 3. */);
    let mut dest_to_src = HashMap::new();
    for (src, _, register) in schedule.inputs() {
        let dest = allocation.choose_destination(register);
        match dest_to_src.entry(dest) {
            Entry::Occupied(_) => { panic!("Two Inputs in the same register"); },
            Entry::Vacant(entry) => { entry.insert(src); },
        }
    }
    for (dest, src) in moves(dest_to_src, TEMP_VALUE) {
        allocation.actions.push(Action::Move(dest, src));
    }
    for (node, _, register) in schedule.iter() {
        allocation.node(node, register);
    }
    // 5. Match `after`.
    let dest_to_src: HashMap<_, _> = after.live_values.iter().map(|&dest| {
        let node = simulation.lookup(dest);
        let src = allocation.lookup(&node);
        (dest, src)
    }).collect();
    for (dest, src) in moves(dest_to_src, TEMP_VALUE) {
        allocation.actions.push(Action::Move(dest, src));
    }
    // Return.
    allocation.actions
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nop() {
        let before = Convention {
            discriminant: Value::Register(ALLOCATABLE_REGISTERS[0]),
            live_values: vec![],
        };
        let actions = vec![];
        let after = Convention {
            discriminant: Value::Register(ALLOCATABLE_REGISTERS[0]),
            live_values: vec![],
        };
        let observed = optimize(before, actions, after);
        let expected: Vec<Action> = vec![];
        assert_eq!(observed.as_slice(), expected.as_slice());
    }
}
