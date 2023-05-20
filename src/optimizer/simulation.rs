use std::collections::{HashMap};
use std::fmt::{Debug};
use super::code::{Precision, Register, Slot, Variable, Convention, Action, Switch, EBB, Ending};
use super::{Exit, CFT, Op, Dataflow, Node, LookupLeaf};

/// Represents the state of an abstract execution of some code which builds a
/// [`Dataflow`] graph.
///
/// The state is updated by [`Action`]s and cloned by [`Switch`]es.
#[derive(Debug, Clone)]
pub struct Simulation {
    /// The number of `Slot`s on the stack.
    slots_used: usize,
    /// Maps each [`Variable`] to the corresponding [`Node`].
    bindings: HashMap<Variable, Node>,
    /// The most recent [`Op::Guard`] or [`Op::Debug`], if any, otherwise the
    /// undefined `Node`.
    sequence: Node,
}

impl Simulation {
    /// Constructs an initial [`Simulation`] representing the entry point of
    /// `dataflow`, which obeys `before`.
    fn new(dataflow: &Dataflow, before: &Convention) -> Self {
        assert_eq!(dataflow.inputs().len(), before.lives.len());
        let bindings = before.lives.iter()
            .zip(dataflow.inputs())
            .map(|(&v, &node)| (v, node))
            .collect();
        Simulation {
            slots_used: before.slots_used,
            bindings: bindings,
            sequence: dataflow.undefined(),
        }
    }

    /// Returns a [`Variable`] representing the top of the stack.
    fn top(&self) -> Variable {
        assert!(self.slots_used > 0);
        Slot(self.slots_used - 1).into()
    }

    /// Returns the [`Node`] that is bound to `value`.
    fn lookup(&self, value: Variable) -> Node {
        *self.bindings.get(&value).expect("Read a dead value")
    }

    /// Binds `dest` to the same [`Variable`] as `src`.
    fn move_(&mut self, dest: Variable, src: Variable) {
        let node = self.lookup(src);
        self.bindings.insert(dest, node);
    }

    /// Binds `dest` to a dead value.
    fn drop(&mut self, dest: Variable) {
        self.bindings.remove(&dest);
    }

    /// Returns a [`Node`] representing `op` applied to `ins`.
    /// Side-effect dependencies are deduced from `op`.
    /// Binds `out` to the `Node`'s output, if any.
    fn op(
        &mut self,
        dataflow: &mut Dataflow,
        op: Op,
        ins: &[Variable],
        out: impl Into<Option<Register>>,
    ) -> Node {
        let mut in_nodes = Vec::new();
        if matches!(op, Op::Guard | Op::Load(_, _) | Op::Store(_, _) | Op::Debug) {
            in_nodes.push(self.sequence);
        }
        for &in_ in ins {
            in_nodes.push(self.lookup(in_));
        }
        // TODO: Common subexpression elimination.
        // TODO: Peephole optimizations.
        let node = dataflow.add_node(op, &in_nodes);
        if let Some(r) = out.into() { self.bindings.insert(r.into(), node); }
        node
    }

    /// Simulate executing `action`, adding to `dataflow` as necessary.
    pub fn action(&mut self, dataflow: &mut Dataflow, action: &Action) {
        match *action {
            Action::Move(dest, src) => {
                self.move_(dest, src);
            },
            Action::Constant(prec, dest, mut value) => {
                if prec == Precision::P32 {
                    // TODO: Remove `prec` from `Action::Constant`.
                    value &= 0xffffffff;
                }
                let _ = self.op(dataflow, Op::Constant(value), &[], dest);
            },
            Action::Unary(un_op, prec, dest, src) => {
                let _ = self.op(dataflow, Op::Unary(prec, un_op), &[src], dest);
            },
            Action::Binary(bin_op, prec, dest, src1, src2) => {
                let _ = self.op(dataflow, Op::Binary(prec, bin_op), &[src1, src2], dest);
            },
            Action::Load(dest, addr) => {
                let _ = self.op(dataflow, Op::Load(addr.offset, addr.width), &[addr.base], dest);
            },
            Action::Store(dest, src, addr) => {
                let _ = self.op(dataflow, Op::Store(addr.offset, addr.width), &[src, addr.base], dest);
            },
            Action::Send(dest, src1, src2) => {
                let _ = self.op(dataflow, Op::Send, &[src1, src2], dest);
            },
            Action::Push(src1, src2) => {
                for src in [src2, src1] {
                    self.slots_used += 1;
                    if let Some(src) = src {
                        self.move_(self.top(), src);
                    }
                }
            },
            Action::Drop(n) => {
                for _ in 0..(2 * n) {
                    self.drop(self.top());
                    self.slots_used -= 1;
                }
            },
            Action::Debug(src) => {
                let node = self.op(dataflow, Op::Debug, &[src], None);
                self.sequence = node;
            },
        };
    }

    /// Simulate executing a guard, adding to `dataflow` as necessary.
    /// Returns the [`Op::Guard`] [`Node`]
    ///  - discriminant - the [`Variable`] tested by the guard.
    pub fn guard(&mut self, dataflow: &mut Dataflow, discriminant: Variable) -> Node {
        let guard = self.op(dataflow, Op::Guard, &[discriminant], None);
        self.sequence = guard;
        guard
    }

    /// Simulate every control-flow path in `ebb`, adding to `dataflow` as
    /// necessary. Returns a [`CFT`] and its total weight.
    fn walk<L: LookupLeaf>(mut self, dataflow: &mut Dataflow, ebb: &EBB<L::Leaf>, lookup_leaf: &L)
    -> (CFT<L::Leaf>, usize) {
        for action in &*ebb.actions {
            self.action(dataflow, action);
        }
        match ebb.ending {
            Ending::Leaf(ref leaf) => {
                let after = lookup_leaf.after(leaf);
                assert_eq!(self.slots_used, after.slots_used);
                let exit = Exit {
                    sequence: self.sequence,
                    outputs: after.lives.iter().map(|&in_| self.lookup(in_)).collect(),
                };
                (CFT::Merge {exit, leaf: leaf.clone()}, lookup_leaf.weight(leaf))
            },
            Ending::Switch(discriminant, Switch {ref cases, ref default_}) => {
                let guard = self.guard(dataflow, discriminant);
                // Recurse on all branches and study the weights.
                let (default_, mut hot_weight) = self.clone().walk(dataflow, default_, lookup_leaf);
                let mut hot_index = usize::MAX;
                let mut total_weight = hot_weight;
                let cases: Box<[_]> = cases.iter().enumerate().map(|(i, case)| {
                    let (case, weight) = self.clone().walk(dataflow, case, lookup_leaf);
                    if weight > hot_weight {
                        hot_index = i;
                        hot_weight = weight;
                    }
                    total_weight += weight;
                    case
                }).collect();
                (CFT::switch(guard, cases, default_, hot_index), total_weight)
            }
        }
    }
}

/// Construct a [`Dataflow`] and a [`CFT`] that include all the operations in
/// `input`.
pub fn simulate<L: LookupLeaf>(before: &Convention, input: &EBB<L::Leaf>, lookup_leaf: &L)
-> (Dataflow, CFT<L::Leaf>) {
    let mut dataflow = Dataflow::new(before.lives.len());
    let simulation = Simulation::new(&dataflow, before);
    let (cft, _) = simulation.walk(&mut dataflow, input, lookup_leaf);
    (dataflow, cft)
}
