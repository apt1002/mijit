use std::collections::{HashMap, HashSet};
use std::fmt::{Debug};

use crate::util::{ArrayMap};
use super::{Op, Dataflow, Node, Out, flood, Cold, CFT};

//-----------------------------------------------------------------------------

/** Represents what happens when a particular [`Op::Guard`] fails. */
#[derive(Debug, PartialEq, Eq)]
pub struct GuardFailure<L: Debug + Clone> {
    /**
     * The HotPathTrees that could be entered as a result of this
     * `GuardFailure`.
     */
    pub cold: Cold<HotPathTree<L>>,
    /**
     * The set of `Out`s that any of `cases` depends on. On the hot path, the
     * `Out`s must be kept alive at least until the [`Op::Guard`] is executed.
     */
    pub keep_alives: HashSet<Out>,
}

/**
 * Represents a tree of (acyclic) hot paths. A hot path is defined to be the
 * set of [`Node`]s that will be executed if all [`Op::Guard`]s have their
 * expected outcomes. If a `Guard` fails, then we end up on a new hot path,
 * which we consider to be a child of the original. This gives a tree
 * structure.
 */
#[derive(Debug, PartialEq, Eq)]
pub struct HotPathTree<L: Debug + Clone> {
    /** The exit [`Node`] of the hot path. */
    pub exit: Node,
    /** The leaf of the hot path. */
    pub leaf: L,
    /** A [`GuardFailure`] for each [`Op::Guard`] on the root hot path. */
    pub children: HashMap<Node, GuardFailure<L>>,
}

impl<L: Debug + Clone> HotPathTree<L> {
    pub fn new(
        exit: Node,
        leaf: L,
        children: impl IntoIterator<Item=GuardFailure<L>>,
    ) -> Self {
        let children = HashMap::from_iter(children.into_iter().map(
            |gf| (gf.cold.guard, gf)
        ));
        HotPathTree {exit, leaf, children}
    }
}

//-----------------------------------------------------------------------------

struct KeepAlive<'a> {
    dataflow: &'a Dataflow,
    marks: ArrayMap<Node, usize>,
}

impl<'a> KeepAlive<'a> {
    fn new(dataflow: &'a Dataflow) -> Self {
        let mut marks = dataflow.node_map();
        marks[dataflow.entry_node()] = 1;
        KeepAlive {dataflow, marks}
    }

    /**
     * Convert `cft` into a [`HotPathTree`].
     *
     * On entry and on exit, `marks[node]` must be in `1..coldness` if
     * `node` is on the hotter path from which `cft` diverges, and `0`
     * otherwise. `marks[entry_node]` must be `1`.
     *
     * - coldness - 2 + the number of cold branches needed to reach `cft`.
     *   (`0` is used for unmarked nodes, and `1` for the entry node).
     */
    fn walk<L: Debug + Clone>(&mut self, cft: &'a CFT<L>, inputs: &mut HashSet<Out>, coldness: usize)
    -> HotPathTree<L> {
        let (colds, exit, leaf) = cft.hot_path();
        // Mark everything that `exit` depends on.
        let nodes = flood(&self.dataflow, &mut self.marks, coldness, inputs, &mut HashSet::new(), exit);
        // For each guard we passed...
        let children: Vec<_> = colds.into_iter().map(|cold| {
            // Recurse to find all the inputs of any cold path.
            let mut keep_alives = HashSet::new();
            let cold = cold.map(|&c| self.walk(c, &mut keep_alives, coldness + 1));
            // Add them to our own inputs if necessary.
            for &out in &keep_alives {
                let (node, _) = self.dataflow.out(out);
                assert_ne!(self.marks[node], 0);
                if self.marks[node] < coldness {
                    // Hotter than us.
                    inputs.insert(out);
                }
            }
            GuardFailure {cold, keep_alives}
        }).collect();
        // Unmark everything that we marked.
        for &node in &*nodes {
            assert_eq!(self.marks[node], coldness);
            self.marks[node] = 0;
        }
        // Construct a HotPathTree.
        let hpt = HotPathTree::new(exit, leaf.clone(), children);
        // Check that all guard [`Node`]s in `nodes` are in `children`.
        for &node in &*nodes {
            if self.dataflow.op(node) == Op::Guard {
                assert!(hpt.children.contains_key(&node));
            }
        }
        // Return.
        hpt
    }
}

/**
 * For each [`Op::Guard`] in `cft`, finds the set of [`Out`]s that
 * are computed on the hot path but which must outlive the `Guard` because they
 * are also needed on at least one cold path.
 */
pub fn keep_alive_sets<L: Debug + Clone>(dataflow: &Dataflow, cft: &CFT<L>) -> HotPathTree<L> {
    let mut ka = KeepAlive::new(dataflow);
    ka.walk(cft, &mut HashSet::new(), 2)
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{CFT, Dataflow, Op};

    impl<L: Debug + Clone> GuardFailure<L> {
        pub fn new(
            guard: Node,
            hot_index: usize,
            keep_alives: impl IntoIterator<Item=Out>,
            colds: impl Into<Box<[HotPathTree<L>]>>,
        ) -> Self {
            let colds = colds.into();
            let keep_alives = HashSet::from_iter(keep_alives);
            GuardFailure {cold: Cold {guard, hot_index, colds}, keep_alives}
        }
    }

    /**
     * ```
     * if a { // guard1, switch1. kas: [c, r, s]
     *     if b { // guard2, switch2. kas: [q]
     *         return p; // hot_hot, merge4
     *     } else {
     *         return q; // hot_cold, merge5
     *     }
     * } else {
     *     if c { // guard3, switch3. kas: [s]
     *         return r; // cold_hot, merge6
     *     } else {
     *         return s; // cold_cold, merge7
     *     }
     * }
     * ```
     */
    #[test]
    fn binary_tree() {
        // Dummy `Leaf`.
        #[derive(Debug, Clone, PartialEq)]
        struct Leaf;
        // Dataflow
        let mut dataflow = Dataflow::new(7);
        let ins: Box<[_]> = dataflow.outs(dataflow.entry_node()).collect();
        let a = ins[0];
        let b = ins[1];
        let c = ins[2];
        let p = ins[3];
        let q = ins[4];
        let r = ins[5];
        let s = ins[6];
        let guard1 = dataflow.add_node(Op::Guard, &[], &[a], 0);
        let guard2 = dataflow.add_node(Op::Guard, &[], &[b], 0);
        let guard3 = dataflow.add_node(Op::Guard, &[], &[c], 0);
        let hot_hot = dataflow.add_node(Op::Convention, &[guard1, guard2], &[p], 0);
        let hot_cold = dataflow.add_node(Op::Convention, &[guard1, guard2], &[q], 0);
        let cold_hot = dataflow.add_node(Op::Convention, &[guard1, guard3], &[r], 0);
        let cold_cold = dataflow.add_node(Op::Convention, &[guard1, guard3], &[s], 0);
        // CFT
        let merge4 = CFT::Merge {exit: hot_hot, leaf: Leaf};
        let merge5 = CFT::Merge {exit: hot_cold, leaf: Leaf};
        let merge6 = CFT::Merge {exit: cold_hot, leaf: Leaf};
        let merge7 = CFT::Merge {exit: cold_cold, leaf: Leaf};
        let switch2 = CFT::switch(guard2, [merge4], merge5, 0);
        let switch3 = CFT::switch(guard3, [merge6], merge7, 0);
        let switch1 = CFT::switch(guard1, [switch2], switch3, 0);
        // Test
        let expected = HotPathTree::new(hot_hot, Leaf, [
            GuardFailure::new(guard1, 0, [c, r, s], [
                HotPathTree::new(cold_hot, Leaf, [
                    GuardFailure::new(guard3, 0, [s], [
                        HotPathTree::new(cold_cold, Leaf, []),
                    ]),
                ]),
            ]),
            GuardFailure::new(guard2, 0, [q], [
                HotPathTree::new(hot_cold, Leaf, []),
            ]),
        ]);
        let observed = keep_alive_sets(&dataflow, &switch1);
        assert_eq!(observed, expected);
    }
}
