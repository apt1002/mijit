use std::fmt::{self, Debug, Formatter};

use crate::util::{AsUsize, CommaSeparated};
use super::{Dep, Op, Cost, op_cost};

//-----------------------------------------------------------------------------

/// A node in a Dataflow graph. Also represents the value it computes.
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub struct Node(usize);

impl Debug for Node {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "Node({})", self.0)
    }
}

impl AsUsize for Node {
    fn as_usize(self) -> usize { self.0 }
}

//-----------------------------------------------------------------------------

/// Helper for `<Dataflow as Debug>::fmt()`. Represents a Node.
struct NodeAdapter<'a> {
    dataflow: &'a Dataflow,
    node: Node,
}

impl<'a> Debug for NodeAdapter<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:?} <- {:?} ({:?})",
            self.node,
            self.dataflow.op(self.node),
            CommaSeparated(|| self.dataflow.ins(self.node)),
        )
    }
}

//-----------------------------------------------------------------------------

/// The information remembered about a [`Node`].
#[derive(Clone)]
struct Info {
    /// What kind of operation the `Node` represents.
    op: Op,
    /// A cache of `op::deps()`.
    deps: &'static [Dep],
    /// A cache of [`Dataflow::cost`]`(op)`.
    cost: &'static Cost,
    /// The index in [`Dataflow::ins`] of the first input of the `Node`.
    start_in: usize,
}

/// Represents a dataflow graph of some code. The nodes are [`Node`]s.
///
/// There is a dummy [`Op::Input`] for the undefined value and for each
/// [`Variable`] that is live on entry to the [`Dataflow`].
///
/// [`Variable`]: super::code::Variable
#[derive(Clone)]
pub struct Dataflow {
    /// The undefined value, also used for null side-effects.
    undefined: Node,
    /// One per [`Node`].
    nodes: Vec<Info>,
    /// One per input. Connects the input to the [`Node`] that computes it.
    ins: Vec<Node>,
}

impl Dataflow {
    /// Construct a `Dataflow` with `num_inputs` values live on entry.
    pub fn new() -> Self {
        let mut ret = Dataflow {
            undefined: Node(0),
            nodes: Vec::new(),
            ins: Vec::new(),
        };
        let node = ret.add_node(Op::Input, &[]);
        assert_eq!(node, ret.undefined);
        ret
    }

    /// Returns the [`Node`] that represents the undefined value. This is
    /// considered to cost nothing and to be executed first.
    pub fn undefined(&self) -> Node {
        self.undefined
    }

    /// Returns the [`Info`] about `node`.
    fn info(&self, node: Node) -> &Info {
        &self.nodes[node.as_usize()]
    }

    /// Returns an [`Op`] indicating what kind of operation `node` represents.
    pub fn op(&self, node: Node) -> Op {
        self.info(node).op
    }

    /// Equivalent to [`op_cost`]`(self.op(node))` but faster.
    pub fn cost(&self, node: Node) -> &'static Cost {
        self.info(node).cost
    }

    /// Returns the [`Node`]s which compute the inputs of `node`.
    pub fn ins(&self, node: Node) -> &[Node] {
        let info = self.info(node);
        &self.ins[info.start_in..][..info.deps.len()]
    }

    /// Applies `callback` to each non-`None` input of `node`.
    pub fn each_input(&self, node: Node, mut callback: impl FnMut(Node, Dep)) {
        let info = self.info(node);
        for (&dep, &in_) in info.deps.iter().zip(&self.ins[info.start_in..]) {
            callback(in_, dep);
        }
    }

    /// Returns the [`Node`] that computes the discriminant of `guard`.
    /// Panics if `guard` is not an [`Op::Guard`].
    pub fn discriminant(&self, guard: Node) -> Node {
        let info = self.info(guard);
        assert_eq!(info.op, Op::Guard);
        self.ins[info.start_in + 1]
    }

    /// Returns whether `node` computes a result.
    pub fn has_out(&self, node: Node) -> bool {
        self.cost(node).latency != 0xFF
    }

    /// Construct a [`Node`] and append it to the graph.
    pub fn add_node(&mut self, op: Op, ins: &[Node]) -> Node {
        let deps = op.deps();
        assert_eq!(ins.len(), deps.len());
        for (&in_, &dep) in ins.iter().zip(deps) {
            if dep.is_value() { assert!(self.has_out(in_)); }
        }
        let cost = op_cost(op);
        let start_in = self.ins.len();
        let node = Node(self.nodes.len());
        self.ins.extend(ins);
        self.nodes.push(Info {op, deps, cost, start_in});
        node
    }

    /// Returns all [`Node`]s in the order they were added.
    pub fn all_nodes(&self) -> impl Iterator<Item=Node> {
        (0..self.nodes.len()).map(|i| Node(i))
    }
}

impl Debug for Dataflow {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        f.write_str("Dataflow")?;
        f.debug_list().entries(self.all_nodes().map(
            |n| NodeAdapter {dataflow: self, node: n}
        )).finish()
    }
}
