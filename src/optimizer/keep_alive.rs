use std::collections::{HashMap, HashSet};

use crate::util::{ArrayMap};
use super::{Dataflow, Node, Out, CFT};

//-----------------------------------------------------------------------------

/** The state of a LIFO flood fill through a [`Dataflow`] graph. */
struct Flood<'a> {
    /** The graph to flood fill. */
    dataflow: &'a Dataflow,
    /** Records which [`Node`]s have been visited. */
    marks: &'a mut ArrayMap<Node, usize>,
    /** The value to store in `marks` when we visit a [`Node`]. */
    temperature: usize,
    /** Accumulates the live inputs. */
    inputs: &'a mut HashSet<Out>,
    /** Accumulates the visited [`Node`]s, topologically sorted. */
    nodes: Vec<Node>,
}

impl <'a> Flood<'a> {
    pub fn new(
        dataflow: &'a Dataflow,
        marks: &'a mut ArrayMap<Node, usize>,
        temperature: usize,
        inputs: &'a mut HashSet<Out>,
    ) -> Self {
        Self {dataflow, marks, temperature, inputs, nodes: Vec::new()}
    }

    /**
     * Flood the unmarked [`Node`]s on which `node` depends.
     *
     * The fill follows `dataflow` dependencies (both values and side-effects)
     * backwards in time. Visited [`Node`]s are marked with `temperature`,
     * and are added to `nodes` after all of their dependencies. The fill stops
     * at [`Node`]s that are marked with a non-zero value; the [`Out`]s by
     * which they are reached are added to `inputs`.
     */
    pub fn flood(&mut self, node: Node) {
        assert_eq!(self.marks[node], 0);
        self.marks[node] = self.temperature;
        // TODO: Sort `Node`s by latency or breadth or something.
        for &node in self.dataflow.deps(node) {
            if self.marks[node] == 0 {
                self.flood(node);
            }
        }
        for &out in self.dataflow.ins(node) {
            let (node, _) = self.dataflow.out(out);
            if self.marks[node] == 0 {
                self.flood(node);
            } else if self.marks[node] < self.temperature {
                self.inputs.insert(out);
            } else {
                assert_eq!(self.marks[node], self.temperature);
            }
        }
        self.nodes.push(node);
    }
}

//-----------------------------------------------------------------------------

struct KeepAlive<'a> {
    dataflow: &'a Dataflow,
    marks: ArrayMap<Node, usize>,
    keep_alives: HashMap<Node, Box<[Out]>>,
}

impl<'a> KeepAlive<'a> {
    fn new(dataflow: &'a Dataflow) -> Self {
        let mut marks = dataflow.node_map();
        marks[dataflow.entry_node()] = 1;
        let keep_alives = HashMap::new();
        KeepAlive {dataflow, marks, keep_alives}
    }

    /**
     * Add to `self.keep_alives` the keep-alive set for every [`Op::Guard`] in
     * `cft`. Add to `inputs` the live inputs of `cft`.
     *
     * On entry and on exit, `marks[node]` must be in `1..temperature` if
     * `node` is on the hotter path from which `cft` diverges, and `0`
     * otherwise. `marks[entry_node]` must be `1`.
     *
     * - temperature - the number of cold branches needed to reach `cft` + 2.
     *   (`0` is used for unmarked nodes, and `1` for the entry node).
     */
    fn walk(&mut self, cft: &'a CFT, inputs: &mut HashSet<Out>, temperature: usize) {
        let (hot_colds, exit) = cft.hot_path();
        // Mark everything that `exit` depends on.
        let mut flood = Flood::new(&self.dataflow, &mut self.marks, temperature, inputs);
        flood.flood(exit);
        let nodes = flood.nodes;
        // For each guard we passed...
        for hot_cold in hot_colds {
            // Recurse to find all the inputs of any cold path.
            let mut keep_alives = HashSet::new();
            for cold in hot_cold.colds {
                self.walk(cold, &mut keep_alives, temperature + 1);
            }
            let keep_alives: Box<[_]> = keep_alives.into_iter().collect();
            // Add them to our own inputs if necessary.
            for &out in &*keep_alives {
                let (node, _) = self.dataflow.out(out);
                assert_ne!(self.marks[node], 0);
                if self.marks[node] < temperature {
                    // Hotter than us.
                    inputs.insert(out);
                }
            }
            // Record them in `self.keep_alives`.
            self.keep_alives.insert(hot_cold.guard, keep_alives);
        }
        // Unark everything that we marked.
        for node in nodes {
            assert_eq!(self.marks[node], temperature);
            self.marks[node] = 0;
        }
    }
}

/**
 * For each [`Op::Guard`] in `cft`, finds the set of [`Out`]s that
 * are computed on the hot path but which must outlive the `Guard` because they
 * are also needed on at least one cold path.
 */
pub fn keep_alive_sets(dataflow: &Dataflow, cft: &CFT) -> HashMap<Node, Box<[Out]>> {
    let mut ka = KeepAlive::new(dataflow);
    ka.walk(cft, &mut HashSet::new(), 2);
    ka.keep_alives
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{Leaf, CFT, Dataflow, Op};
    use crate::util::{AsUsize};

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
        let switch2 = CFT::Switch {guard: guard2, hot_index: 0, cases: Box::new([merge4]), default_: Box::new(merge5)};
        let switch3 = CFT::Switch {guard: guard3, hot_index: 0, cases: Box::new([merge6]), default_: Box::new(merge7)};
        let switch1 = CFT::Switch {guard: guard1, hot_index: 0, cases: Box::new([switch2]), default_: Box::new(switch3)};
        // Test
        let expected = {
            let mut ret: HashMap<Node, Box<[Out]>> = HashMap::new();
            ret.insert(guard1, Box::new([c, r, s]));
            ret.insert(guard2, Box::new([q]));
            ret.insert(guard3, Box::new([s]));
            ret
        };
        let mut observed = keep_alive_sets(&dataflow, &switch1);
        // Sort for comparison.
        for set in observed.values_mut() {
            set.sort_by_key(|out| out.as_usize());
        }
        assert_eq!(observed, expected);
    }
}
