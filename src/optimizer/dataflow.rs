use std::fmt::{self, Debug, Formatter};

use crate::util::{AsUsize, ArrayMap, CommaSeparated};
use super::{Op, Cost, op_cost};

//-----------------------------------------------------------------------------

array_index! {
    /// A node in a Dataflow graph.
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct Node(std::num::NonZeroUsize) {
        debug_name: "Node",
        UInt: usize,
    }
}

array_index! {
    /// A value produced by a [`Node`] in a Dataflow graph.
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct Out(std::num::NonZeroUsize) {
        debug_name: "Out",
        UInt: usize,
    }
}

//-----------------------------------------------------------------------------

/// Helper for `<Dataflow as Debug>::fmt()`. Represents a Node.
struct NodeAdapter<'a> {
    dataflow: &'a Dataflow,
    node: Node,
}

impl<'a> Debug for NodeAdapter<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:?}: ({:?}) <- {:?} ({:?})",
            self.node,
            CommaSeparated(|| self.dataflow.outs(self.node)),
            self.dataflow.op(self.node),
            CommaSeparated(|| self.dataflow.ins(self.node)),
        )?;
        let deps = self.dataflow.deps(self.node);
        if !deps.is_empty() {
            write!(f, " after ({:?})", CommaSeparated(|| deps))?;
        }
        Ok(())
    }
}

//-----------------------------------------------------------------------------

/// The internal representation of a [`Node`].
#[derive(Clone)]
struct Info {
    /// What kind of operation the `Node` represents.
    op: Op,
    /// A cache of [`Dataflow::op_cost(op)`].
    cost: &'static Cost,
    /// The index in [`Dataflow::deps`] after the last dep of the `Node`.
    end_dep: usize,
    /// The index in [`Dataflow::ins`] after the last input of the `Node`.
    end_in: usize,
    /// The index in [`Dataflow::outs`] after the last [`Out`] of the `Node`.
    end_out: usize,
}

/// Represents a dataflow graph of some code.
/// The nodes are [`Node`]s and the edges are [`Out`]s.
///
/// There is a dummy `Node` that has an output for each [`Value`] that is live
/// on entry to the [`Dataflow`].
///
/// [`Value`]: super::code::Value
#[derive(Clone)]
pub struct Dataflow {
    /// One per [`Node`].
    nodes: Vec<Info>,
    /// One per non-dataflow dependency: a predecessor [`Node`].
    deps: Vec<Node>,
    /// One per input. Connects the input to the [`Out`].
    ins: Vec<Out>,
    /// One per [`Out`]: the [`Node`] that generates the `Out`.
    outs: Vec<Node>,
}

impl Dataflow {
    /// Construct a `Dataflow` with `num_inputs` values live on entry.
    pub fn new(num_inputs: usize) -> Self {
        let mut ret = Dataflow {
            nodes: Vec::new(),
            deps: Vec::new(),
            ins: Vec::new(),
            outs: Vec::new(),
        };
        ret.add_node(Op::Convention, &[], &[], num_inputs);
        ret
    }

    /// Returns the entry [`Node`].
    pub fn entry_node(&self) -> Node {
        Node::new(0).unwrap()
    }

    /// Returns the [`Info`] about `node`.
    fn info(&self, node: Node) -> &Info {
        &self.nodes[node.as_usize()]
    }

    /// Returns an [`Op`] indicating what kind of operation `node` represents.
    pub fn op(&self, node: Node) -> Op {
        self.info(node).op
    }

    /// Equivalent to `op_cost(self.op(node))` but faster.
    pub fn cost(&self, node: Node) -> &'static Cost {
        self.info(node).cost
    }

    /// Tests whether `node` is the dummy [`Node`] that represents the Values
    /// that are live on entry to the Dataflow.
    pub fn is_entry(&self, node: Node) -> bool {
        node.as_usize() == 0
    }

    /// Returns the [`Info`] about the previous `node`, if any.
    fn prev(&self, node: Node) -> Option<&Info> {
        if self.is_entry(node) {
            None
        } else {
            Some(&self.nodes[node.as_usize() - 1])
        }
    }

    /// Returns the [`Node`]s which must be executed before `node`.
    pub fn deps(&self, node: Node) -> &[Node] {
        let start_dep = self.prev(node).map_or(0, |prev| prev.end_dep);
        &self.deps[start_dep .. self.info(node).end_dep]
    }

    /// Returns the [`Out`]s which are consumed by the inputs of `node`.
    pub fn ins(&self, node: Node) -> &[Out] {
        let start_in = self.prev(node).map_or(0, |prev| prev.end_in);
        &self.ins[start_in .. self.info(node).end_in]
    }

    /// Returns the number of [`Out`]s which are produced by `node`.
    pub fn num_outs(&self, node: Node) -> usize {
        let start_out = self.prev(node).map_or(0, |prev| prev.end_out);
        self.info(node).end_out - start_out
    }

    /// Returns the [`Out`]s which are produced by `node`.
    pub fn outs(&self, node: Node) -> impl Iterator<Item=Out> {
        let start_out = self.prev(node).map_or(0, |prev| prev.end_out);
        (start_out .. self.info(node).end_out).map(|index| Out::new(index).unwrap())
    }

    /// Returns the [`Node`] which produces `out`, and the index of `out` among
    /// the outputs of the `Node`.
    pub fn out(&self, out: Out) -> (Node, usize) {
        let node = self.outs[out.as_usize()];
        let start_out = self.prev(node).map_or(0, |prev| prev.end_out);
        (node, out.as_usize() - start_out)
    }

    pub fn add_node(&mut self, op: Op, deps: &[Node], ins: &[Out], num_outs: usize) -> Node {
        let node = Node::new(self.nodes.len()).unwrap();
        self.deps.extend(deps);
        self.ins.extend(ins);
        self.outs.extend((0..num_outs).map(|_| node));
        self.nodes.push(Info {
            op: op,
            cost: op_cost(op),
            end_dep: self.deps.len(),
            end_in: self.ins.len(),
            end_out: self.outs.len(),
        });
        node
    }

    /// Returns a fresh ArrayMap that initally associates `V::default()` with
    /// each [`Node`] of this Dataflow.
    pub fn node_map<V: Default>(&self) -> ArrayMap<Node, V> {
        ArrayMap::new(self.nodes.len())
    }

    /// Returns a fresh ArrayMap that initally associates `V::default()` with
    /// each output of each [`Node`] of this Dataflow.
    pub fn out_map<V: Default>(&self) -> ArrayMap<Out, V> {
        ArrayMap::new(self.outs.len())
    }

    /// Returns all [`Node`]s in the order they were added.
    pub fn all_nodes(&self) -> impl Iterator<Item=Node> {
        (0..self.nodes.len()).map(|i| Node::new(i).unwrap())
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
