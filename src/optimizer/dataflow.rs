use std::fmt::{self, Debug, Formatter};

use crate::util::{AsUsize, ArrayMap, CommaSeparated};
use super::{Op, Cost, op_cost};

//-----------------------------------------------------------------------------

array_index! {
    /// A node in a Dataflow graph. Also represents the value it computes.
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct Node(std::num::NonZeroUsize) {
        debug_name: "Node",
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
        write!(f, "{:?} <- {:?} ({:?})",
            self.node,
            self.dataflow.op(self.node),
            CommaSeparated(|| self.dataflow.ins(self.node)),
        )?;
        if let Some(dep) = self.dataflow.dep(self.node) {
            write!(f, " after ({:?})", dep)?;
        }
        Ok(())
    }
}

//-----------------------------------------------------------------------------

/// The information remembered about a [`Node`].
#[derive(Clone)]
struct Info {
    /// What kind of operation the `Node` represents.
    op: Op,
    /// A cache of [`Dataflow::cost`]`(op)`.
    cost: &'static Cost,
    /// A `Node` whose side-effects must happen before the `Node`, if any.
    dep: Option<Node>,
    /// The index in [`Dataflow::ins`] after the last input of the `Node`.
    end_in: usize,
}

/// Represents a dataflow graph of some code. The nodes are [`Node`]s.
///
/// There is a dummy [`Op::Input`] `Node` for each [`Variable`] that is live
/// on entry to the [`Dataflow`].
///
/// [`Variable`]: super::code::Variable
#[derive(Clone)]
pub struct Dataflow {
    /// The live values on entry.
    inputs: Box<[Node]>,
    /// One per [`Node`].
    nodes: Vec<Info>,
    /// One per input. Connects the input to the [`Node`] that computes it.
    ins: Vec<Node>,
}

impl Dataflow {
    /// Construct a `Dataflow` with `num_inputs` values live on entry.
    pub fn new(num_inputs: usize) -> Self {
        let mut ret = Dataflow {
            inputs: (0..num_inputs).map(|i| Node::new(i).unwrap()).collect(),
            nodes: Vec::new(),
            ins: Vec::new(),
        };
        for i in 0..num_inputs {
            let node = ret.add_node(Op::Input, None, &[]);
            assert_eq!(node, ret.inputs[i]);
        }
        ret
    }

    /// Returns the [`Node`]s representing the values live on entry.
    pub fn inputs(&self) -> &[Node] {
        &self.inputs
    }

    /// Returns the [`Info`] about `node`.
    fn info(&self, node: Node) -> &Info {
        &self.nodes[node.as_usize()]
    }

    /// Returns an [`Op`] indicating what kind of operation `node` represents.
    pub fn op(&self, node: Node) -> Op {
        self.info(node).op
    }

    /// Tests whether `node` is an [`Op::Load`].
    pub fn is_load(&self, node: Node) -> bool {
        matches!(self.op(node), Op::Load(_))
    }

    /// Equivalent to [`op_cost`]`(self.op(node))` but faster.
    pub fn cost(&self, node: Node) -> &'static Cost {
        self.info(node).cost
    }

    /// Returns the [`Info`] about the previous `node`, if any.
    fn prev(&self, node: Node) -> Option<&Info> {
        node.as_usize().checked_sub(1).map(|i| &self.nodes[i])
    }

    /// Returns the [`Node`] which must be executed before `node`, if any.
    pub fn dep(&self, node: Node) -> Option<Node> {
        self.info(node).dep
    }

    /// Returns the [`Node`]s which compute the inputs of `node`.
    pub fn ins(&self, node: Node) -> &[Node] {
        let start_in = self.prev(node).map_or(0, |prev| prev.end_in);
        &self.ins[start_in .. self.info(node).end_in]
    }

    /// Returns whether `node` computes a result.
    pub fn has_out(&self, node: Node) -> bool {
        self.cost(node).output_latency.is_some()
    }

    /// Construct a [`Node`] and append it to the graph.
    pub fn add_node(&mut self, op: Op, dep: Option<Node>, ins: &[Node]) -> Node {
        let node = Node::new(self.nodes.len()).unwrap();
        self.ins.extend(ins);
        self.nodes.push(Info {op, cost: op_cost(op), dep, end_in: self.ins.len()});
        node
    }

    /// Returns a fresh ArrayMap that initally associates `V::default()` with
    /// each [`Node`] of this Dataflow.
    pub fn node_map<V: Default>(&self) -> ArrayMap<Node, V> {
        ArrayMap::new(self.nodes.len())
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
