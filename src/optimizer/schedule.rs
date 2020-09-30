use std::{cmp};
use std::collections::{HashMap};

use crate::util::{RcEq};
use super::dataflow::{Node};
use super::pressure::{Pressure};

pub const PARALLELISM: usize = 3;

/** Records all information about one cycle of the schedule. */
struct Cycle {
    /** Execution resources not yet used in this cycle. */
    pub available: usize,
    /** Instructions we intend to execute in this cycle, in reverse order. */
    pub nodes: Vec<RcEq<Node>>,
}

impl Cycle {
    pub fn new() -> Self {
        Cycle {available: PARALLELISM, nodes: Vec::new()}
    }

    fn fits(&self, node: &RcEq<Node>) -> bool {
        self.available >= node.op.cost()
    }
}

//-----------------------------------------------------------------------------

/** Usage information about a Node in a WorkList. */
struct Usage {
    /** The number of Nodes which depend on this one. */
    pub num_uses: usize,
    /** The cycle by which this Node must be available. */
    pub born_cycle: usize,
    /** The cycle after which this Node is no longer needed. */
    pub dies_cycle: usize,
}

impl Usage {
    pub fn new() -> Self {
        Usage {num_uses: 1, born_cycle: 0, dies_cycle: usize::MAX}
    }
}

/** Usage information about Nodes in a WorkList. */
struct WorkList {
    /** Usage for every Node on which any of the `roots` depends. */
    pub infos: HashMap<RcEq<Node>, Usage>,
}

impl WorkList {
    pub fn new() -> Self {
        WorkList {infos: HashMap::new()}
    }

    /**
     * Ensure that all dependencies of `node` are in `infos`, incrementing
     * usage counts as we go.
     */
    pub fn find_dependencies(&mut self, node: &RcEq<Node>) {
        if let Some(usage) = self.infos.get_mut(&node) {
            // We have already seen this Node.
            usage.num_uses += 1;
        } else {
            for (o, _) in node.op.operands() {
                self.find_dependencies(o);
            }
            for d in node.op.dependencies() {
                self.find_dependencies(d);
            }
            self.infos.insert(node.clone(), Usage::new());
        }
    }

    /**
     * Add `node` and its unshared dependencies to `schedule`, decrementing
     * usage counts as we go.
     */
    pub fn schedule(
        &mut self,
        node: &RcEq<Node>,
        cycle: usize,
        schedule: &mut Schedule,
    ) {
        let usage = self.infos.get_mut(node).unwrap();
        usage.born_cycle = std::cmp::max(usage.born_cycle, cycle);
        usage.dies_cycle = std::cmp::min(usage.dies_cycle, cycle);
        assert!(usage.num_uses > 0);
        usage.num_uses -= 1;
        if usage.num_uses > 0 {
            // We have not yet found all Nodes that depend on `node`.
            // We will revisit it later, via the other Nodes.
            return;
        }

        let cycle = schedule.choose_cycle(node, usage.born_cycle, usage.dies_cycle);

        // Recursively schedule `node`'s dependencies.
        let mut queue = Vec::new();
        for (o, latency) in node.op.operands() {
            queue.push((o, cycle + latency));
        }
        for d in node.op.dependencies() {
            queue.push((d, cycle));
        }
        // TODO: Sort `queue`.
        for (i, i_cycle) in queue {
            self.schedule(i, i_cycle, schedule);
        }
    }
}

//-----------------------------------------------------------------------------

struct NodeInfo {
    /** The cycle in which we execute the Node. */
    pub born_cycle: usize,
    /** The cycle after which the result of the Node is no longer needed. */
    pub dies_cycle: usize,
    /** The logical register (if any) which will hold the result. */
    pub register: Option<usize>,
}

/** An instruction schedule. */
pub struct Schedule {
    /** The Cycles we're allocating, in reverse order: 0 is the last Cycle. */
    cycles: Vec<Cycle>,
    /** NodeInfo for every Node in the schedule. */
    infos: HashMap<RcEq<Node>, NodeInfo>,
    /** Register pressure as a function of time. */
    pressure: Pressure<RcEq<Node>>,
}

impl Schedule {
    /**
     * Compute a Schedule that includes each of `roots` and its dependencies.
     */
    pub fn new(roots: Vec<(RcEq<Node>, usize)>) -> Self {
        let mut work_list = WorkList::new();
        for &(ref node, _) in &roots {
            work_list.find_dependencies(node);
        }
        let mut schedule = Schedule {
            cycles: Vec::new(),
            infos: HashMap::new(),
            pressure: Pressure::new(),
        };
        for &(ref node, cycle) in &roots {
            work_list.schedule(node, cycle, &mut schedule)
        }
        schedule
    }

    fn fits(&self, node: &RcEq<Node>, cycle: usize) -> bool {
        if cycle >= self.cycles.len() {
            return true;
        }
        self.cycles[cycle].fits(node)
    }

    /**
     * Finds a cycle in which `node` can be executed. The chosen cycle will be
     * as late as possible but no later than `born_cycle`. `node` is stored in
     * the schedule and its execution resources are deducted.
     */
    pub fn choose_cycle(
        &mut self,
        node: &RcEq<Node>,
        mut born_cycle: usize,
        dies_cycle: usize,
    ) -> usize {
        born_cycle = cmp::max(born_cycle, self.pressure.latest_time_with_unused_register());
        while !self.fits(node, born_cycle) {
            born_cycle += 1;
        }
        while born_cycle <= self.cycles.len() {
            self.cycles.push(Cycle::new());
        }
        self.cycles[born_cycle].nodes.push(node.clone());
        self.cycles[born_cycle].available -= node.op.cost();
        let register = self.pressure
            .allocate_register(born_cycle, dies_cycle, node.clone())
            .map(|(register, previous_node)| {
                if let Some(previous_node) = previous_node {
                    // Steal `register` from `previous_node`. Spill the latter.
                    let mut info = self.infos.get_mut(&previous_node).expect("missing NodeInfo");
                    assert_eq!(info.register, Some(register));
                    info.register = None;
                }
                register
            });
        self.infos.insert(node.clone(), NodeInfo {born_cycle, dies_cycle, register});
        born_cycle
    }
}
