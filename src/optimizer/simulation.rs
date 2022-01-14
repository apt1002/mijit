use std::collections::{HashMap};
use super::code::{Precision, Register, Slot, Variable, Convention, Action, Switch, EBB, Ending};
use super::{CFT, Op, Dataflow, Node, Out, LookupLeaf};

/**
 * Represents the state of an abstract execution of some code which builds a
 * [`Dataflow`] graph.
 *
 * The state is updated by [`Action`]s and cloned by [`Switch`]es.
 */
#[derive(Debug, Clone)]
pub struct Simulation {
    /** The number of `Slot`s on the stack. */
    slots_used: usize,
    /** Maps each [`Variable`] to the corresponding [`Out`]. */
    bindings: HashMap<Variable, Out>,
    /**
     * An instruction whose execution represents successfully passing all
     * preceding [`Op::Guard`] instructions.
     */
    sequence: Node,
    /** The most recent [`Op::Store`] instruction, or the entry node. */
    store: Node,
    /** All [`Op::Load`] instructions since `store`. */
    loads: Vec<Node>,
    /** The most recent debug operation, or the entry node. */
    debug: Node,
}

impl Simulation {
    /**
     * Constructs an initial [`State`] representing the entry point of
     * `dataflow`, which obeys `before`.
     */
    fn new(dataflow: &Dataflow, before: &Convention) -> Self {
        let entry_node = dataflow.entry_node();
        assert_eq!(dataflow.num_outs(entry_node), before.live_values.len());
        let bindings = before.live_values.iter()
            .cloned()
            .zip(dataflow.outs(entry_node))
            .collect();
        Simulation {
            slots_used: before.slots_used,
            bindings: bindings,
            sequence: entry_node,
            store: entry_node,
            loads: vec![],
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

    /** Binds `dest` to the same [`Variable`] as `src`. */
    fn move_(&mut self, dest: Variable, src: Variable) {
        let out = self.lookup(src);
        self.bindings.insert(dest, out);
    }

    /** Binds `dest` to a dead value. */
    fn drop(&mut self, dest: Variable) {
        self.bindings.remove(&dest);
    }

    /**
     * Returns a [`Node`] representing `op` applied to `ins`, depending on
     * `deps`. Binds `outs` to the `Node`'s outputs.
     */
    fn op(&mut self, dataflow: &mut Dataflow, op: Op, deps: &[Node], ins: &[Variable], outs: &[Register]) -> Node {
        let ins: Vec<_> = ins.iter().map(|&in_| self.lookup(in_)).collect();
        // TODO: Common subexpression elimination.
        // TODO: Peephole optimizations.
        let node = dataflow.add_node(op, deps, &ins, outs.len());
        for (out, &r) in dataflow.outs(node).zip(outs) {
            self.bindings.insert(r.into(), out);
        }
        node
    }

    /** Simulate executing `action`, adding to `dataflow` as necessary. */
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
                let _ = self.op(dataflow, Op::Constant(value), &[], &[], &[dest]);
            },
            Action::Unary(un_op, prec, dest, src) => {
                let _ = self.op(dataflow, Op::Unary(prec, un_op), &[], &[src], &[dest]);
            },
            Action::Binary(bin_op, prec, dest, src1, src2) => {
                let _ = self.op(dataflow, Op::Binary(prec, bin_op), &[], &[src1, src2], &[dest]);
            },
            Action::Load(dest, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let node = self.op(dataflow, Op::Load(width, alias_mask), &[self.sequence, self.store], &[addr], &[dest]);
                self.loads.push(node);
            },
            Action::Store(dest, src, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let mut deps = Vec::new();
                std::mem::swap(&mut deps, &mut self.loads);
                deps.push(self.sequence);
                deps.push(self.store);
                let node = self.op(dataflow, Op::Store(width, alias_mask), &deps, &[src, addr], &[dest]);
                self.move_(dest.into(), src);
                self.store = node;
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
                let node = self.op(dataflow, Op::Debug, &[self.sequence, self.debug], &[src], &[]);
                self.debug = node;
            },
        };
    }

    /**
     * Simulate executing a guard, adding to `dataflow` as necessary.
     * Returns the [`Op::Guard`] [`Node`]
     *  - discriminant - the [`Variable`] tested by the guard.
     */
    pub fn guard(&mut self, dataflow: &mut Dataflow, discriminant: Variable) -> Node {
        let discriminant = self.lookup(discriminant);
        let guard = dataflow.add_node(Op::Guard, &[], &[discriminant], 0);
        let sequence = self.op(dataflow, Op::Sequence, &[guard, self.sequence], &[], &[]);
        self.sequence = sequence;
        guard
    }

    /**
     * Add to `dataflow` an exit [`Node`] that depends on all dataflow and
     * non-dataflow outputs. On exit, `after.live_values` are live.
     * Returns the exit `Node`.
     */
    pub fn exit(mut self, dataflow: &mut Dataflow, after: &Convention) -> Node {
        assert_eq!(self.slots_used, after.slots_used);
        let deps = [self.sequence, self.store, self.debug];
        self.op(dataflow, Op::Convention, &deps, &after.live_values, &[])
    }

    /**
     * Simulate every control-flow path in `ebb`, adding to `dataflow` as
     * necessary. Returns a [`CFT`] and its total weight.
     */
    fn walk<L: Clone>(mut self, dataflow: &mut Dataflow, ebb: &EBB<L>, lookup_leaf: &impl LookupLeaf<L>) -> (CFT<L>, usize) {
        for ref action in &ebb.actions {
            self.action(dataflow, action);
        }
        match ebb.ending {
            Ending::Leaf(ref leaf) => {
                let exit = self.exit(dataflow, lookup_leaf.after(leaf));
                (CFT::Merge {exit, leaf: leaf.clone()}, lookup_leaf.weight(leaf))
            },
            Ending::Switch(ref switch) => {
                match *switch {
                    Switch::Always(ref ebb) => self.walk(dataflow, &*ebb, lookup_leaf),
                    Switch::Index {discriminant, ref cases, ref default_} => {
                        let guard = self.guard(dataflow, discriminant);
                        // Recurse on all branches and study the weights.
                        let (default_, mut hot_weight) = self.clone().walk(dataflow, &*default_, lookup_leaf);
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
    }
}

/**
 * Construct a [`Dataflow`] and a [`CFT`] that include all the operations in
 * `input`.
 */
pub fn simulate<L: Clone>(input: &EBB<L>, lookup_leaf: &impl LookupLeaf<L>) -> (Dataflow, CFT<L>) {
    let mut dataflow = Dataflow::new(input.before.live_values.len());
    let simulation = Simulation::new(&dataflow, &input.before);
    let (cft, _) = simulation.walk(&mut dataflow, &input, lookup_leaf);
    (dataflow, cft)
}
