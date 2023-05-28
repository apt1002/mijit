use std::collections::hash_map::{HashMap, Entry};

use super::graph::{dep, Dataflow, Node, Exit};

/// Ways in which the marked [`Node`]s of a [`Fill`] depend on its boundary.
///
/// A mapping from `node` to `dep` indicates that one or more `Node`s in the
/// `Fill` depend on a boundary `Node` `node` in the manner described by `dep`.
#[derive(Debug, Clone, Default)]
pub struct Frontier(pub HashMap<Node, dep::Value>);

/// The state of a flood fill through a [`Dataflow`] graph.
pub struct Fill<'a> {
    /// The graph to flood fill.
    dataflow: &'a Dataflow,
    /// Records [`Node`]s which have been marked:
    /// - `0..marker` means a boundary: a `Node` that should not be marked.
    /// - `marker` means marked.
    marks: &'a mut HashMap<Node, usize>,
    /// The value to store in `marks` when we mark a [`Node`].
    marker: usize,
    /// The marked [`Node`]s, in an arbitrary order.
    nodes: Vec<Node>,
    /// Accumulates the dependencies of the marked [`Node`]s.
    frontier: Frontier,
}

impl<'a> Fill<'a> {
    /// Constructs a `Fill` with no boundary.
    pub fn new(dataflow: &'a Dataflow, marks: &'a mut HashMap<Node, usize>) -> Self {
        Fill {
            dataflow,
            marks,
            marker: 0,
            nodes: Vec::new(),
            frontier: Frontier::default(),
        }
    }

    /// Constructs a `Fill` whose boundary is the union of the boundary of
    /// `self` and [`Node`]s marked by `self`.
    pub fn nested(&mut self) -> Fill<'_> {
        Fill {
            dataflow: self.dataflow,
            marks: self.marks,
            marker: self.marker + 1,
            nodes: Vec::new(),
            frontier: Frontier::default(),
        }
    }

    pub fn dataflow(&self) -> &'a Dataflow { self.dataflow }

    /// Assert that all non-boundary depdendencies of `node` are marked, and
    /// that `node` is non-boundary and unmarked. Then, mark it.
    ///
    /// Note: this method is not useful for flood-filling; use `input` instead.
    pub fn mark(&mut self, node: Node) {
        self.dataflow.each_input(node, |in_, _| assert!(self.marks.contains_key(&in_)));
        assert!(!self.marks.contains_key(&node));
        self.marks.insert(node, self.marker);
        self.nodes.push(node);
    }

    /// If `node` is in the boundary, add it to `frontier`. Otherwise, if
    /// `node` is unmarked, add it to `marks` and `nodes`.
    fn enqueue(&mut self, node: Node, dep: dep::Value) {
        match self.marks.entry(node) {
            Entry::Occupied(e) => {
                if *e.get() < self.marker {
                    // `node` is on the boundary.
                    let v = self.frontier.0.entry(node).or_insert(dep::Value::Unused);
                    *v = std::cmp::max(*v, dep);
                }
            },
            Entry::Vacant(e) => {
                e.insert(self.marker);
                self.nodes.push(node);
            },
        }
    }

    /// Mark `node` and all its dependencies. Add boundary [`Node`]s to
    /// the [`Frontier`].
    pub fn input(&mut self, node: Node, node_dep: dep::Value) {
        let mut done = self.nodes.len();
        self.enqueue(node, node_dep);
        while done < self.nodes.len() {
            let node = self.nodes[done];
            done += 1;
            self.dataflow.each_input(node, |in_, in_dep| self.enqueue(in_, in_dep.0));
        }
    }

    /// Mark all dependencies of `Exit`.
    pub fn exit(&mut self, exit: &Exit) {
        self.input(exit.sequence, dep::Value::Unused);
        for &node in &*exit.outputs { self.input(node, dep::Value::Normal); }
    }

    /// Call [`input`] on each [`Node`] in `frontier`. This method can be used
    /// to resume a flood fill with a smaller boundary set.
    ///
    /// [`input`]: Self::input
    pub fn resume(&mut self, frontier: &Frontier) {
        for (&input, &dep) in &frontier.0 { self.input(input, dep); }
    }

    /// See the marked [`Node`]s.
    pub fn nodes(&self) -> impl '_ + Iterator<Item=Node> { self.nodes.iter().copied() }

    /// Unmarks and returns the marked [`Node`]s and their dependencies.
    pub fn drain(&mut self) -> (Vec<Node>, Frontier) {
        let mut frontier = Frontier::default();
        std::mem::swap(&mut frontier, &mut self.frontier);
        let mut nodes = Vec::new();
        std::mem::swap(&mut nodes, &mut self.nodes);
        for &node in &nodes { self.marks.remove(&node); }
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

/// Construct a `marks` array, wrap it in a [`Fill`], and invoke `callback`.
/// The [`Input`] [`Node`]s will be treated as boundary nodes.
///
/// [`Input`]: super::Op::Input
pub fn with_fill<T>(
    dataflow: &Dataflow,
    callback: impl FnOnce(Fill) -> T,
) -> T {
    let mut marks = HashMap::new();
    let mut fill = Fill::new(dataflow, &mut marks);
    fill.mark(dataflow.undefined());
    for &node in dataflow.inputs() { fill.mark(node); }
    callback(fill.nested())
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{code, graph};
    use code::{Precision, BinaryOp, Width};
    use graph::{Op};
    use Precision::*;
    use crate::util::{AsUsize};

    #[test]
    fn test() {
        // Construct a `Dataflow` with two exits and a dead `Node`.
        // TODO: Use `Send`.
        let mut df = Dataflow::new(1);
        let u = df.undefined();
        let a = df.inputs()[0];
        let guard = df.add_node(Op::Guard, &[u, a]);
        let constant = df.add_node(Op::Constant(1), &[]);
        let b = constant;
        let add = df.add_node(Op::Binary(P64, BinaryOp::Add), &[a, b]);
        let c = add;
        let exit1 = Exit {sequence: guard, outputs: Box::new([c])};
        let store = df.add_node(Op::Store(0, Width::Eight), &[guard, b, a]);
        let d = store;
        let exit2 = Exit {sequence: store, outputs: Box::new([d])};
        let mul = df.add_node(Op::Binary(P64, BinaryOp::Mul), &[b, b]);
        let e = mul;
        // Mark `entry` with `1`.
        let mut marks = HashMap::new();
        let mut fill = Fill::new(&df, &mut marks);
        fill.input(u, dep::Value::Unused);
        fill.input(a, dep::Value::Normal);
        // Flood from `exit1`.
        let mut fill1 = fill.nested();
        fill1.exit(&exit1);
        let (mut nodes1, frontier1) = fill1.drain();
        nodes1.sort_by_key(|&node| node.as_usize());
        assert_eq!(&nodes1, &[guard, constant, add]);
        assert_eq!(frontier1.0.len(), 2);
        assert_eq!(frontier1.0[&u], dep::Value::Unused);
        assert_eq!(frontier1.0[&a], dep::Value::Normal);
        for node in nodes1 { fill1.mark(node); }
        // Nested flood from `exit2`.
        let mut fill2 = fill1.nested();
        fill2.exit(&exit2);
        let (mut nodes2, frontier2) = fill2.drain();
        nodes2.sort_by_key(|&node| node.as_usize());
        assert_eq!(&nodes2, &[store]);
        assert_eq!(frontier2.0.len(), 3);
        assert_eq!(frontier2.0[&a], dep::Value::Address);
        assert_eq!(frontier2.0[&b], dep::Value::Normal);
        assert_eq!(frontier2.0[&guard], dep::Value::Unused);
        for node in nodes2 { fill2.mark(node); }
        // Check the marks.
        assert_eq!(marks.len(), 6);
        assert_eq!(marks.get(&u), Some(&0));
        assert_eq!(marks.get(&a), Some(&0));
        assert_eq!(marks.get(&guard), Some(&1));
        assert_eq!(marks.get(&b), Some(&1));
        assert_eq!(marks.get(&c), Some(&1));
        assert_eq!(marks.get(&d), Some(&2));
        assert_eq!(marks.get(&e), None);
    }
}
