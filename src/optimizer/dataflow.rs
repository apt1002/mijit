use crate::util::{AsUsize, ArrayMap};
use super::{Op};
use super::code::{Value};

//-----------------------------------------------------------------------------

/** A node in a Dataflow graph. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Node(usize);

impl AsUsize for Node {
    fn as_usize(self) -> usize { self.0 }
}

/** A value produced by a [`Node`] in a Dataflow graph. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Out(usize);

impl AsUsize for Out {
    fn as_usize(self) -> usize { self.0 }
}

//-----------------------------------------------------------------------------

/** The internal representation of a [`Node`]. */
#[derive(Debug, Clone)]
struct Info {
    /** What kind of operation the Node represents. */
    op: Op,
    /** The index in [`Dataflow::deps`] after the last dep of the Node. */
    end_dep: usize,
    /** The index in [`Dataflow::ins`] after the last In of the Node. */
    end_in: usize,
    /** The index in [`Dataflow::outs`] after the last Out of the Node. */
    end_out: usize,
}

/**
 * Represents a dataflow graph of some code.
 * The nodes are [`Node`]s, and edges lead from an [`Out`] to an [`In`].
 *
 * There is a dummy `Node` that has an output for each [`Value`] that is live
 * on entry to the Dataflow.
 */
#[derive(Debug, Clone)]
pub struct Dataflow {
    /** The inputs of the whole graph. */
    inputs: Vec<Value>,
    /** One per Node. */
    nodes: Vec<Info>,
    /** One per non-dataflow dependency. Gives a predecessor Node. */
    deps: Vec<Node>,
    /** One per In. Connects the In to the Out. */
    ins: Vec<Out>,
    /** One per Out. Gives the Node that generates the Out. */
    outs: Vec<Node>,
}

impl Dataflow {
    pub fn new(inputs: Vec<Value>) -> Self {
        let mut ret = Dataflow {
            inputs,
            nodes: Vec::new(),
            deps: Vec::new(),
            ins: Vec::new(),
            outs: Vec::new(),
        };
        ret.add_node(Op::Convention, &[], &[], ret.inputs().len());
        ret
    }

    /** Returns the `inputs` of this [`Dataflow`] (as passed to `new()`). */
    pub fn inputs(&self) -> &[Value] {
        self.inputs.as_ref()
    }

    /** Returns the entry [`Node`]. */
    pub fn entry_node(&self) -> Node {
        Node(0)
    }

    /** Returns the [`Info`] about `node`. */
    fn info(&self, node: Node) -> &Info {
        &self.nodes[node.as_usize()]
    }

    /**
     * Returns an [`Op`] indicating what kind of operation `node` represents.
     */
    pub fn node(&self, node: Node) -> Op {
        self.info(node).op
    }

    /**
     * Tests whether `node` is the dummy [`Node`] that represents the Values
     * that are live on entry to the Dataflow.
     */
    pub fn is_entry(&self, node: Node) -> bool {
        node.as_usize() == 0
    }

    /** Returns the [`Info`] about the previous `node`, if any. */
    fn prev(&self, node: Node) -> Option<&Info> {
        if self.is_entry(node) {
            None
        } else {
            Some(&self.nodes[node.as_usize() - 1])
        }
    }

    /** Returns the [`Node`]s which must be executed before `node`. */
    pub fn deps(&self, node: Node) -> &[Node] {
        let start_dep = if let Some(prev) = self.prev(node) {
            prev.end_dep
        } else {
            0
        };
        &self.deps[start_dep .. self.info(node).end_dep]
    }

    /** Returns the [`Out`]s which are consumed by the inputs of `node`. */
    pub fn ins(&self, node: Node) -> &[Out] {
        let start_in = if let Some(prev) = self.prev(node) {
            prev.end_in
        } else {
            0
        };
        &self.ins[start_in .. self.info(node).end_in]
    }

    /** Returns the [`Out`]s which are produced by `node`. */
    pub fn outs(&self, node: Node) -> impl Iterator<Item=Out> {
        let start_out = if let Some(prev) = self.prev(node) {
            prev.end_out
        } else {
            0
        };
        (start_out .. self.info(node).end_out).map(|index| Out(index))
    }

    /**
     * Returns the [`Node`] which produces `out`, and the index of `out` among
     * the outputs of the `Node`.
     */
    pub fn out(&self, out: Out) -> (Node, usize) {
        let node = self.outs[out.as_usize()];
        let start_out = if let Some(prev) = self.prev(node) {
            prev.end_out
        } else {
            0
        };
        (node, out.as_usize() - start_out)
    }

    pub fn add_node(&mut self, op: Op, deps: &[Node], ins: &[Out], num_outs: usize) -> Node {
        let node = Node(self.nodes.len());
        self.deps.extend(deps);
        self.ins.extend(ins);
        self.outs.extend((0..num_outs).map(|_| node));
        self.nodes.push(Info {
            op: op,
            end_dep: self.deps.len(),
            end_in: self.ins.len(),
            end_out: self.outs.len(),
        });
        node
    }

    /**
     * Returns a fresh ArrayMap that initally associates `V::default()` with
     * each [`Node`] of this Dataflow.
     */
    pub fn node_map<V: Default>(&self) -> ArrayMap<Node, V> {
        ArrayMap::new(self.nodes.len())
    }

    /**
     * Returns a fresh ArrayMap that initally associates `V::default()` with
     * each output of each [`Node`] of this Dataflow.
     */
    pub fn out_map<V: Default>(&self) -> ArrayMap<Out, V> {
        ArrayMap::new(self.outs.len())
    }
}
