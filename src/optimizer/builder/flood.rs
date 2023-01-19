use std::collections::{HashSet};

use super::{Dataflow, Node, Out};
use crate::util::{ArrayMap};

/// The state of a LIFO flood fill through a [`Dataflow`] graph.
#[derive(Debug)]
struct Flood<'a> {
    /// The graph to flood fill.
    dataflow: &'a Dataflow,
    /// Records which [`Node`]s have been visited.
    marks: &'a mut ArrayMap<Node, usize>,
    /// The value to store in `marks` when we visit a [`Node`].
    marker: usize,
    /// Accumulates the live inputs.
    inputs: &'a mut HashSet<Out>,
    /// Accumulates the direct dependencies.
    effects: &'a mut HashSet<Node>,
    /// Accumulates the visited [`Node`]s, topologically sorted.
    nodes: Vec<Node>,
}

impl <'a> Flood<'a> {
    /// The recursive part of `flood()`.
    pub fn visit(&mut self, node: Node) {
        assert_eq!(self.marks[node], 0);
        self.marks[node] = self.marker;
        // TODO: Sort `Node`s by latency or breadth or something.
        for &node in self.dataflow.deps(node) {
            if self.marks[node] == 0 {
                self.visit(node);
            } else if self.marks[node] < self.marker {
                self.effects.insert(node);
            } else {
                assert_eq!(self.marks[node], self.marker);
            }
        }
        for &out in self.dataflow.ins(node) {
            let (node, _) = self.dataflow.out(out);
            if self.marks[node] == 0 {
                self.visit(node);
            } else if self.marks[node] < self.marker {
                self.inputs.insert(out);
            } else {
                assert_eq!(self.marks[node], self.marker);
            }
        }
        self.nodes.push(node);
    }
}

/// Flood fill the unmarked [`Node`]s on which `exit_node` depends.
///
/// The fill follows `dataflow` dependencies (both values and side-effects)
/// backwards in time. Visited `Node`s are marked with `marker`. The fill stops
/// at `Node`s that are marked with a non-zero value; the [`Out`]s by which they
/// are reached are added to `inputs` and those `Node`s whose side-effects are
/// needed are added to `effects`.
///
/// Returns the `Node`s that were marked. The returned array is topologically
/// sorted into a possible execution order.
pub fn flood(
    dataflow: &Dataflow,
    marks: &mut ArrayMap<Node, usize>,
    marker: usize,
    inputs: &mut HashSet<Out>,
    effects: &mut HashSet<Node>,
    exit_node: Node,
) -> Box<[Node]> {
    let mut f = Flood {dataflow, marks, marker, inputs, effects, nodes: Vec::new()};
    f.visit(exit_node);
    f.nodes.into()
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{code, Op};
    use code::{Precision, BinaryOp, Width, AliasMask};
    use Precision::*;
    use crate::util::{AsUsize};

    #[test]
    fn test() {
        // Construct a `Dataflow` with two exits and a dead `Node`.
        let mut df = Dataflow::new(1);
        let entry = df.entry_node();
        let a = df.outs(entry).next().unwrap();
        let guard = df.add_node(Op::Guard, &[], &[a], 0);
        let constant = df.add_node(Op::Constant(1), &[], &[], 1);
        let b = df.outs(constant).next().unwrap();
        let add = df.add_node(Op::Binary(P64, BinaryOp::Add), &[], &[a, b], 1);
        let c = df.outs(add).next().unwrap();
        let exit1 = df.add_node(Op::Convention, &[guard, entry], &[c], 0);
        let store = df.add_node(Op::Store(Width::Eight, AliasMask(1)), &[entry, guard], &[b, a], 1);
        let d = df.outs(store).next().unwrap();
        let exit2 = df.add_node(Op::Convention, &[guard, store], &[d], 0);
        let _ = df.add_node(Op::Binary(P64, BinaryOp::Mul), &[], &[b, b], 1);
        // Mark `entry` with `1`.
        let mut marks = df.node_map();
        marks[entry] = 1;
        // Flood from `exit1` with colour `11`.
        let mut inputs1 = HashSet::new();
        let mut effects1 = HashSet::new();
        let nodes1 = flood(&df, &mut marks, 11, &mut inputs1, &mut effects1, exit1);
        assert_eq!(&*nodes1, &[guard, constant, add, exit1]);
        let mut inputs1 = Vec::from_iter(inputs1);
        inputs1.sort_by_key(|out| out.as_usize());
        assert_eq!(&inputs1, &[a]);
        let mut effects1 = Vec::from_iter(effects1);
        effects1.sort_by_key(|node| node.as_usize());
        assert_eq!(&effects1, &[entry]);
        // Flood from `exit2` with colour `12`.
        let mut inputs2 = HashSet::new();
        let mut effects2 = HashSet::new();
        let nodes2 = flood(&df, &mut marks, 12, &mut inputs2, &mut effects2, exit2);
        assert_eq!(&*nodes2, &[store, exit2]);
        let mut inputs2 = Vec::from_iter(inputs2);
        inputs2.sort_by_key(|out| out.as_usize());
        assert_eq!(&inputs2, &[a, b]);
        let mut effects2 = Vec::from_iter(effects2);
        effects2.sort_by_key(|node| node.as_usize());
        assert_eq!(&effects2, &[entry, guard]);
        // Check the marks.
        assert_eq!(marks.as_ref(), &[1, 11, 11, 11, 11, 12, 12, 0]);
    }
}
