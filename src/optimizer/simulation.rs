use std::collections::{HashMap};
use super::code::{Precision, Register, Slot, Variable, Action};
use super::{Convention};
use super::{Dataflow, Node, Op, Out};

/**
 * Represents the state of a simulated execution of some [`Action`]s.
 */
#[derive(Debug)]
pub struct Simulation {
    /** The [`Dataflow`] which is being built. */
    dataflow: Dataflow,
    /** The number of `Slot`s on the stack. */
    slots_used: usize,
    /** Maps each [`Variable`] to the corresponding [`Out`]. */
    bindings: HashMap<Variable, Out>,
    /** The most recent [`Op::Store`] instruction, or the entry node. */
    store: Node,
    /** All memory accesses instructions since `store`, including `store`. */
    loads: Vec<Node>,
    /** The most recent debug operation, or the entry node. */
    debug: Node,
}

impl Simulation {
    /**
     * Constructs a `Simulation` of a basic block. On entry, only `inputs` are
     * live.
     */
    pub fn new(before: &Convention) -> Self {
        let dataflow = Dataflow::new(before.live_values.len());
        let entry_node = dataflow.entry_node();
        let bindings = before.live_values.iter()
            .cloned()
            .zip(dataflow.outs(entry_node))
            .collect();
        Simulation {
            dataflow: dataflow,
            slots_used: before.slots_used,
            bindings: bindings,
            store: entry_node,
            loads: vec![entry_node],
            debug: entry_node,
        }
    }

    /** Returns a [`Variable`] representing the top of the stack. */
    fn top(&self) -> Variable {
        assert!(self.slots_used > 0);
        Slot(self.slots_used - 1).into()
    }

    /** Returns the [`Out`] that is bound to `value`. */
    fn lookup(&self, value: Variable) -> Out {
        *self.bindings.get(&value).expect("Read a dead value")
    }

    /**
     * Returns a [`Node`] representing `op` applied to `ins`, depending on
     * `deps`. Binds `outs` to the `Node`'s outputs.
     */
    fn op(&mut self, op: Op, deps: &[Node], ins: &[Variable], outs: &[Register]) -> Node {
        let ins: Vec<_> = ins.iter().map(|&in_| self.lookup(in_)).collect();
        // TODO: Common subexpression elimination.
        // TODO: Peephole optimizations.
        let node = self.dataflow.add_node(op, deps, &ins, outs.len());
        for (out, &r) in self.dataflow.outs(node).zip(outs) {
            self.bindings.insert(r.into(), out);
        }
        node
    }

    /** Binds `dest` to the same [`Variable`] as `src`. */
    fn move_(&mut self, dest: Variable, src: Variable) {
        let out = self.lookup(src);
        self.bindings.insert(dest, out);
    }

    /** Binds `dest` to a dead value. */
    fn drop(&mut self, dest: Variable) {
        self.bindings.remove(&dest);
    }

    /** Simulate executing `action`. */
    pub fn action(&mut self, action: &Action) {
        match *action {
            Action::Move(dest, src) => {
                self.move_(dest, src);
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
            Action::Store(dest, src, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let mut deps = Vec::new();
                std::mem::swap(&mut deps, &mut self.loads);
                let node = self.op(Op::Store(width, alias_mask), &deps, &[src, addr], &[dest]);
                self.move_(dest.into(), src);
                self.store = node;
                self.loads.push(node);
            },
            Action::Push(src1, src2) => {
                for src in [src2, src1] {
                    self.slots_used += 1;
                    if let Some(src) = src {
                        self.move_(self.top(), src);
                    }
                }
            },
            Action::Pop(dest1, dest2) => {
                for dest in [dest1, dest2] {
                    if let Some(dest) = dest {
                        self.move_(dest.into(), self.top());
                    }
                    self.drop(self.top());
                    self.slots_used -= 1;
                }
            },
            Action::DropMany(n) => {
                for _ in 0..(2 * n) {
                    self.drop(self.top());
                    self.slots_used -= 1;
                }
            },
            Action::Debug(src) => {
                let node = self.op(Op::Debug, &[self.debug], &[src], &[]);
                self.debug = node;
            },
        };
    }

    /**
     * Appends an exit [`Node`] that depends on all dataflow and non-dataflow
     * outputs. On exit, `outputs` are live.
     * Returns the finished `Dataflow` graph and the exit `Node`.
     */
    pub fn finish(mut self, after: &Convention) -> (Dataflow, Node) {
        assert_eq!(self.slots_used, after.slots_used);
        let exit_node = self.op(Op::Convention, &[self.store, self.debug], &after.live_values, &[]);
        (self.dataflow, exit_node)
    }
}
