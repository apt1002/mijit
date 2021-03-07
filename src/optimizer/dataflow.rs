use crate::util::{AsUsize};
use super::{Op};
use super::code::{Value};

//-----------------------------------------------------------------------------

/** A node in a Dataflow graph. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Node(usize);

impl AsUsize for Node {
    fn as_usize(self) -> usize { self.0 }
}

/** Connects a [`Node`] that produces a value to one that consumes it. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Edge(usize);

impl AsUsize for Edge {
    fn as_usize(self) -> usize { self.0 }
}

//-----------------------------------------------------------------------------

/** The internal representation of a [`Node`]. */
#[derive(Debug, Clone)]
struct Info {
    /** What kind of operation the Node represents. */
    op: Op,
    /** The index in [`Dataflow::outs`] after the last Out of the Node. */
    last_out: usize,
    /** The index in [`Dataflow::ins`] after the last In of the Node. */
    last_in: usize,
    /** The index in [`Dataflow::deps`] after the last dep of the Node. */
    last_dep: usize,
    /** The immediate constant of the operation, if any. */
    constant: i64,
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
    /** One per Out. Gives the Node that generates the Out. */
    outs: Vec<Node>,
    /** One per In. Connects the In to the Out. */
    ins: Vec<Edge>,
    /** One per non-dataflow dependency. Gives a predecessor Node. */
    deps: Vec<Node>,
}

impl Dataflow {
    pub fn new(inputs: Vec<Value>) -> Self {
        let entry = Info {
            op: Op::Convention,
            last_out: inputs.len(),
            last_in: 0,
            last_dep: 0,
            constant: 0,
        };
        let outs: Vec<_> = inputs.iter().map(|_| Node(0)).collect();
        Dataflow {
            inputs,
            nodes: vec![entry],
            outs,
            ins: Vec::new(),
            deps: Vec::new(),
        }
    }

    /** Returns the `inputs` of this Dataflow (as passed to `new()`). */
    pub fn inputs(&self) -> &[Value] {
        self.inputs.as_ref()
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

    /** Returns the input [`Edge`]s of `node`. */
    pub fn ins(&self, node: Node) -> &[Edge] {
        if let Some(prev) = self.prev(node) {
            &self.ins[prev.last_in .. self.info(node).last_in]
        } else {
            &self.ins[0..0]
        }
    }

    /**
     * Returns the [`Node`] which produces `out`, and the index of `out` among
     * the outputs of the `Node`.
     */
    pub fn out(&self, out: Edge) -> (Node, usize) {
        let node = self.outs[out.as_usize()];
        let first_out = if let Some(prev) = self.prev(node) {
            prev.last_out
        } else {
            0
        };
        (node, out.as_usize() - first_out)
    }

}
