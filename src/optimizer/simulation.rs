use std::collections::{HashMap};
use super::code::{Value};
use super::{Dataflow, Node, Out};

/**
 * Represents the state of a simulated execution of some [`Action`]s.
 */
#[derive(Debug)]
pub struct Simulation {
    /** The [`Dataflow`] which is being built. */
    dataflow: Dataflow,
    /** Maps each [`Value`] to the corresponding [`Out`]. */
    bindings: HashMap<Value, Out>,
    /** The most recent [`Op::Store`] instruction, or the entry node. */
    store: Node,
    /** All memory accesses instructions since `store`, including `store`. */
    loads: Vec<Node>,
    /** The most recent stack operation, or the entry node. */
    stack: Node,
}

impl Simulation {
    pub fn new(dataflow: Dataflow) -> Self {
        let entry_node = dataflow.entry_node();
        let bindings = dataflow.inputs().iter()
            .cloned()
            .zip(dataflow.outs(entry_node))
            .collect();
        Simulation {
            dataflow: dataflow,
            bindings: bindings,
            store: entry_node,
            loads: Vec::new(),
            stack: entry_node,
        }
    }
}
