use std::collections::{HashMap, HashSet};

use crate::util::{ArrayMap};
use super::{Dataflow, Node, Out, flood, Cold, CFT};

//-----------------------------------------------------------------------------

/** Represents what happens when a particular [`Op::Guard`] fails. */
#[derive(Debug)]
pub struct GuardFailure {
    /**
     * The HotPathTrees that could be entered as a result of this
     * `GuardFailure`.
     */
    pub cold: Cold<HotPathTree>,
    /**
     * The set of `Out`s that any of `cases` depends on. On the hot path, the
     * `Out`s must be kept alive at least until the [`Op::Guard`] is executed.
     */
    pub keep_alives: HashSet<Out>,
}

impl GuardFailure {
    pub fn new(
        guard: Node,
        hot_index: usize,
        colds: impl Into<Box<[HotPathTree]>>,
        keep_alives: HashSet<Out>,
    ) -> Self {
        let colds = colds.into();
        GuardFailure {cold: Cold {guard, hot_index, colds}, keep_alives}
    }
}

/**
 * Represents a tree of (acyclic) hot paths. A hot path is defined to be the
 * set of [`Node`]s that will be executed if all [`Op::Guard`]s have their
 * expected outcomes. If a `Guard` fails, then we end up on a new hot path,
 * which we consider to be a child of the original. This gives a tree
 * structure.
 */
#[derive(Debug)]
pub struct HotPathTree {
    /** The `Node`s that comprise the root hot path, topologically sorted. */
    pub nodes: Box<[Node]>,
    /** A [`GuardFailure`] for each [`Op::Guard`] on the root hot path. */
    pub children: HashMap<Node, GuardFailure>,
}

impl HotPathTree {
    pub fn new(
        nodes: impl Into<Box<[Node]>>,
        children: impl IntoIterator<Item=GuardFailure>,
    ) -> Self {
        let nodes = nodes.into();
        let children = HashMap::from_iter(children.into_iter().map(
            |gf| (gf.cold.guard, gf)
        ));
        HotPathTree {nodes, children}
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
     * On entry and on exit, `marks[node]` must be in `1..temperature` if
     * `node` is on the hotter path from which `cft` diverges, and `0`
     * otherwise. `marks[entry_node]` must be `1`.
     *
     * - temperature - the number of cold branches needed to reach `cft` + 2.
     *   (`0` is used for unmarked nodes, and `1` for the entry node).
     */
    fn walk(&mut self, cft: &'a CFT, inputs: &mut HashSet<Out>, temperature: usize)
    -> HotPathTree {
        let (colds, exit) = cft.hot_path();
        // Mark everything that `exit` depends on.
        let nodes = flood(&self.dataflow, &mut self.marks, temperature, inputs, exit);
        // For each guard we passed...
        let children: Vec<_> = colds.into_iter().map(|cold| {
            // Recurse to find all the inputs of any cold path.
            let mut keep_alives = HashSet::new();
            let cold = cold.map(|&c| self.walk(c, &mut keep_alives, temperature + 1));
            // Add them to our own inputs if necessary.
            for &out in &keep_alives {
                let (node, _) = self.dataflow.out(out);
                assert_ne!(self.marks[node], 0);
                if self.marks[node] < temperature {
                    // Hotter than us.
                    inputs.insert(out);
                }
            }
            GuardFailure {cold, keep_alives}
        }).collect();
        // Unmark everything that we marked.
        for &node in &*nodes {
            assert_eq!(self.marks[node], temperature);
            self.marks[node] = 0;
        }
        // Construct and return a HotPathTree.
        HotPathTree::new(nodes, children)
    }
}

/**
 * For each [`Op::Guard`] in `cft`, finds the set of [`Out`]s that
 * are computed on the hot path but which must outlive the `Guard` because they
 * are also needed on at least one cold path.
 */
pub fn keep_alive_sets(dataflow: &Dataflow, cft: &CFT) -> HotPathTree {
    let mut ka = KeepAlive::new(dataflow);
    ka.walk(cft, &mut HashSet::new(), 2)
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::hash::{Hash};

    use super::*;
    use super::super::{Leaf, CFT, Dataflow, Op};

    /** Returns a duplicate-free slice as a [`HashSet`]. */
    fn as_set<T: Copy + Hash + Eq>(slice: &[T]) -> HashSet<T> {
        let set: HashSet<_> = slice.iter().copied().collect();
        assert_eq!(set.len(), slice.len());
        set
    }

    impl<C: PartialEq> PartialEq<Self> for Cold<C> {
        fn eq(&self, other: &Self) -> bool {
            self.guard == other.guard &&
            self.hot_index == other.hot_index &&
            self.colds == other.colds
        }
    }

    impl PartialEq<Self> for GuardFailure {
        fn eq(&self, other: &Self) -> bool {
            self.cold == other.cold &&
            self.keep_alives == other.keep_alives
        }
    }

    impl PartialEq<Self> for HotPathTree {
        fn eq(&self, other: &Self) -> bool {
            as_set(&*self.nodes) == as_set(&*other.nodes) &&
            self.children == other.children
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
        let expected = HotPathTree::new(
            [guard1, guard2, hot_hot],
            [
                GuardFailure::new(
                    guard1, 0, [
                        HotPathTree::new(
                            [guard3, cold_hot],
                            [
                                GuardFailure::new(
                                    guard3, 0, [
                                        HotPathTree::new([cold_cold], []),
                                    ], HashSet::from_iter([s])
                                ),
                            ],
                        ),
                    ], HashSet::from_iter([c, r, s])
                ),
                GuardFailure::new(
                    guard2, 0, [
                        HotPathTree::new([hot_cold], []),
                    ], HashSet::from_iter([q])
                ),
            ],
        );
        let  observed = keep_alive_sets(&dataflow, &switch1);
        assert_eq!(observed, expected);
    }
}
