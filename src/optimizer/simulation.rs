use std::collections::{HashMap};
use super::code::{Precision, Register, Value, Action};
use super::{Dataflow, Node, Op, Out};

/**
 * Represents the state of a simulated execution of some [`Action`]s.
 */
#[derive(Debug)]
pub struct Simulation {
    /** The [`Dataflow`] which is being built. */
    dataflow: Dataflow,
    /** Maps each [`Value`] to the corresponding [`Out`]. */
    bindings: HashMap<Value, Out>,
    /** The most recent [`Op::Store`] instruction, or the entry node. */
    store: Node,
    /** All memory accesses instructions since `store`, including `store`. */
    loads: Vec<Node>,
    /** The most recent stack operation, or the entry node. */
    stack: Node,
}

impl Simulation {
    pub fn new(dataflow: Dataflow) -> Self {
        let entry_node = dataflow.entry_node();
        let bindings = dataflow.inputs().iter()
            .cloned()
            .zip(dataflow.outs(entry_node))
            .collect();
        Simulation {
            dataflow: dataflow,
            bindings: bindings,
            store: entry_node,
            loads: vec![entry_node],
            stack: entry_node,
        }
    }

    /** Returns the `Out` that is bound to `value`. */
    pub fn lookup(&self, value: Value) -> Out {
        self.bindings.get(&value).expect("Read a dead value").clone()
    }

    /** Returns a Node representing the result of `op`. */
    fn op(&mut self, op: Op, deps: &[Node], ins: &[Value], outs: &[Register]) -> Node {
        let ins: Vec<_> = ins.iter().map(|&in_| self.lookup(in_)).collect();
        let node = self.dataflow.add_node(op, deps, &ins, outs.len());
        for (out, &r) in self.dataflow.outs(node).zip(outs) {
            self.bindings.insert(r.into(), out);
        }
        node
    }

    pub fn action(&mut self, action: &Action) {
        match *action {
            Action::Move(dest, src) => {
                let out = self.lookup(src);
                self.bindings.insert(dest.into(), out);
            },
            Action::Constant(prec, dest, mut value) => {
                if prec == Precision::P32 {
                    // TODO: Remove `prec` from `Action::Constant`.
                    value &= 0xffffffff;
                }
                let _ = self.op(Op::Constant(value), &[], &[], &[dest]);
            },
            Action::Unary(un_op, prec, dest, src) => {
                let _ = self.op(Op::Unary(prec, un_op), &[], &[src], &[dest]);
            },
            Action::Binary(bin_op, prec, dest, src1, src2) => {
                let _ = self.op(Op::Binary(prec, bin_op), &[], &[src1, src2], &[dest]);
            },
            Action::Load(dest, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let node = self.op(Op::Load(width, alias_mask), &[self.store], &[addr], &[dest]);
                self.loads.push(node);
            },
            Action::Store(src, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let mut deps = Vec::new();
                std::mem::swap(&mut deps, &mut self.loads);
                let node = self.op(Op::Store(width, alias_mask), &deps, &[src, addr.into()], &[]);
                self.store = node;
                self.loads.push(node);
            },
            Action::Push(src) => {
                let node = self.op(Op::Push, &[self.stack], &[src], &[]);
                self.stack = node;
            },
            Action::Pop(dest) => {
                let node = self.op(Op::Pop, &[self.stack], &[], &[dest]);
                self.stack = node;
            },
            Action::Debug(src) => {
                let node = self.op(Op::Push, &[self.stack], &[src], &[]);
                self.stack = node;
            },
        };
    }
}
