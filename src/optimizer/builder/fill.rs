use std::collections::{HashSet};

use super::{Dataflow, Node, Out};
use crate::util::{ArrayMap};

/// Ways in which the marked [`Node`]s of a [`Fill`] depends on its boundary.
#[derive(Debug, Clone, Default)]
pub struct Frontier {
    /// The side-effects depended on by the nodes but not performed by them.
    pub effects: HashSet<Node>,
    /// The values depended on by the nodes but not computed by them.
    pub inputs: HashSet<Out>,
}

/// The state of a LIFO flood fill through a [`Dataflow`] graph.
pub struct Fill<'a> {
    /// The graph to flood fill.
    dataflow: &'a Dataflow,
    /// Records which [`Node`]s have been marked:
    /// - `0` means unmarked.
    /// - `1..marker` means a boundary: a `Node` that should not be marked.
    /// - `marker` means marked.
    marks: &'a mut ArrayMap<Node, usize>,
    /// The value to store in `marks` when we mark a [`Node`].
    marker: usize,
    /// The marked [`Node`]s, topologically sorted such that earlier `Node`s
    /// do not depend on later ones.
    nodes: Vec<Node>,
    /// Accumulates the dependencies of the marked [`Node`]s.
    frontier: Frontier,
}

impl<'a> Fill<'a> {
    /// Constructs a `Fill` with no boundary.
    pub fn new(dataflow: &'a Dataflow, marks: &'a mut ArrayMap<Node, usize>) -> Self {
        Fill {dataflow, marks, marker: 1, nodes: Vec::new(), frontier: Frontier::default()}
    }

    /// Constructs a `Fill` whose boundary is the union of the boundary of
    /// `self` and [`Node`]s marked by `self`.
    pub fn nested<'b>(&'b mut self) -> Fill<'b> {
        Fill {
            dataflow: &*self.dataflow,
            marks: &mut *self.marks,
            marker: self.marker + 1,
            nodes: Vec::new(),  
            frontier: Frontier::default(),
        }
    }

    pub fn dataflow(&self) -> &'a Dataflow { self.dataflow }

    /// Assert that all non-boundary depdendencies of `node` are marked, and
    /// that `node` is non-boundary and unmarked. Then, mark it.
    pub fn mark(&mut self, node: Node) {
        for &dep in self.dataflow.deps(node) {
            assert_ne!(self[dep], 0);
        }
        for &in_ in self.dataflow.ins(node) {
            assert_ne!(self[self.dataflow.out(in_).0], 0);
        }
        assert_eq!(self[node], 0);
        self.marks[node] = self.marker;
        self.nodes.push(node);
    }

    /// If `node` is unmarked and not in the boundary, mark it and all of its
    /// dependencies. Returns `true` if `node` is in the boundary.
    pub fn visit(&mut self, node: Node) -> bool {
        if self[node] == 0 {
            // TODO: Sort `Node`s by latency or breadth or something.
            for &dep in self.dataflow.deps(node) { self.effect(dep); }
            for &in_ in self.dataflow.ins(node) { self.input(in_); }
            self.mark(node);
        }
        self[node] < self.marker
    }

    /// Find and mark all dependencies of `effect`.
    pub fn effect(&mut self, effect: Node) {
        if self.visit(effect) {
            self.frontier.effects.insert(effect);
        }
    }

    /// Find and mark all dependencies of `input`.
    pub fn input(&mut self, in_: Out) {
        if self.visit(self.dataflow.out(in_).0) {
            self.frontier.inputs.insert(in_);
        }
    }

    /// Call [`effect`] on each of `frontier.effects` and [`input`] on each of
    /// `frontier.inputs`. This method can be used to resume a flood fill with a
    /// smaller boundary set.
    pub fn resume(&mut self, frontier: &Frontier) {
        for &input in &frontier.inputs { self.input(input); }
        for &effect in &frontier.effects { self.effect(effect); }
    }

    /// See the marked [`Node`]s.
    pub fn nodes(&self) -> impl '_ + Iterator<Item=Node> { self.nodes.iter().copied() }

    /// Unmarks and returns the marked [`Node`]s and their dependencies.
    pub fn drain(&mut self) -> (Vec<Node>, Frontier) {
        let mut frontier = Frontier::default();
        std::mem::swap(&mut frontier, &mut self.frontier);
        let mut nodes = Vec::new();
        std::mem::swap(&mut nodes, &mut self.nodes);
        for &node in &nodes { self.marks[node] = 0; }
        (nodes, frontier)
    }
}

impl<'a> std::fmt::Debug for Fill<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Fill")
            .field("marker", &self.marker)
            .field("nodes", &self.nodes)
            .field("frontier", &self.frontier)
            .finish()
    }
}

impl<'a> std::ops::Index<Node> for Fill<'a> {
    type Output = usize;
    fn index(&self, index: Node) -> &Self::Output { &self.marks[index] }
}

/// Construct a `marks` array, wrap it in a [`Fill`], and invoke `callback`.
/// `dataflow.entry_node()` will be treated as a boundary node.
pub fn with_fill<T>(
    dataflow: &Dataflow,
    callback: impl FnOnce(Fill) -> T,
) -> T {
    let mut marks = dataflow.node_map();
    let mut fill = Fill::new(dataflow, &mut marks);
    fill.mark(dataflow.entry_node());
    callback(fill.nested())
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
        let mut fill = Fill::new(&df, &mut marks);
        fill.mark(entry);
        // Flood from `exit1` with colour `2`.
        let mut fill1 = fill.nested();
        let is_boundary1 = fill1.visit(exit1);
        assert!(!is_boundary1);
        let (nodes1, frontier1) = fill1.drain();
        assert_eq!(&nodes1, &[guard, constant, add, exit1]);
        let mut inputs1 = Vec::from_iter(frontier1.inputs);
        inputs1.sort_by_key(|out| out.as_usize());
        assert_eq!(&inputs1, &[a]);
        let mut effects1 = Vec::from_iter(frontier1.effects);
        effects1.sort_by_key(|node| node.as_usize());
        assert_eq!(&effects1, &[entry]);
        for node in nodes1 { fill1.mark(node); }
        // Flood from `exit2` with colour `12`.
        let mut fill2 = fill1.nested();
        let is_boundary2 = fill2.visit(exit2);
        assert!(!is_boundary2);
        let (nodes2, frontier2) = fill2.drain();
        assert_eq!(&nodes2, &[store, exit2]);
        let mut inputs2 = Vec::from_iter(frontier2.inputs);
        inputs2.sort_by_key(|out| out.as_usize());
        assert_eq!(&inputs2, &[a, b]);
        let mut effects2 = Vec::from_iter(frontier2.effects);
        effects2.sort_by_key(|node| node.as_usize());
        assert_eq!(&effects2, &[entry, guard]);
        for node in nodes2 { fill2.mark(node); }
        // Check the marks.
        assert_eq!(marks.as_ref(), &[1, 2, 2, 2, 2, 3, 3, 0]);
    }
}
