use std::{cmp};
use std::collections::{HashMap};

use crate::util::{RcEq};
use super::dataflow::{Node};
use super::pressure::{Life, Pressure};

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

    fn fits(&self, node: &Node) -> bool {
        self.available >= node.op.cost()
    }
}

//-----------------------------------------------------------------------------

/** Time is measured in cycles backwards from the end of the Schedule. */
pub type Time = cmp::Reverse<usize>;

pub const EARLY: Time = cmp::Reverse(usize::MAX);
pub const LATE: Time = cmp::Reverse(0);

/**
 * Usage information about a Node in a WorkList. Information is collected
 * incrementally as references to the Node are processed.
 */
struct Usage {
    /** The number of Nodes which depend on the Node. */
    pub num_uses: usize,
    /** The lifetime of the result of the Node. */
    pub life: Life<Time>,
}

impl Usage {
    pub fn new() -> Self {
        Usage {num_uses: 1, life: Life::new(LATE, EARLY)}
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
     * usage counts as we go, such that the result of `node` is valid for at
     * least `life`.
     */
    pub fn schedule(
        &mut self,
        node: &RcEq<Node>,
        life: Life<Time>,
        schedule: &mut Schedule,
    ) {
        let usage = self.infos.get_mut(node).unwrap();
        usage.life |= life;
        assert!(usage.num_uses > 0);
        usage.num_uses -= 1;
        if usage.num_uses > 0 {
            // We have not yet found all Nodes that depend on `node`.
            // We will revisit it later, via the other Nodes.
            return;
        }

        // We have all the required info about `node`. Schedule it.
        schedule.choose_cycle(node, &mut usage.life);

        // Operands of `node` must live until the result is born.
        let dies = usage.life.born;

        // Recursively schedule `node`'s dependencies.
        let mut queue = Vec::new();
        for (o, latency) in node.op.operands() {
            let born = cmp::Reverse(dies.0 + latency);
            queue.push((o, Life::new(born, dies)));
        }
        for d in node.op.dependencies() {
            queue.push((d, Life::new(dies, dies)));
        }
        // TODO: Sort `queue`.
        for (i, life) in queue {
            // FIXME: No need to allocate a register for dependencies!
            self.schedule(i, life, schedule);
        }
    }
}

//-----------------------------------------------------------------------------

struct NodeInfo {
    /** The lifetime of the result of the Node. */
    pub life: Life<Time>,
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
    pressure: Pressure<Time, RcEq<Node>>,
}

impl Schedule {
    /**
     * Compute a Schedule that includes each of `roots` and its dependencies.
     */
    pub fn new(roots: Vec<(RcEq<Node>, Time)>) -> Self {
        let mut work_list = WorkList::new();
        for &(ref node, _) in &roots {
            work_list.find_dependencies(node);
        }
        let mut schedule = Schedule {
            cycles: Vec::new(),
            infos: HashMap::new(),
            pressure: Pressure::new(|| LATE),
        };
        for &(ref node, time) in &roots {
            work_list.schedule(node, Life::new(time, time), &mut schedule)
        }
        schedule
    }

    fn fits(&self, node: &Node, cycle: usize) -> bool {
        if cycle >= self.cycles.len() {
            return true;
        }
        self.cycles[cycle].fits(node)
    }

    /**
     * Finds a cycle in which `node` can be executed. The chosen cycle will be
     * as late as possible but no later than `life.born`. `life.born` is
     * set to the chosen cycle. `node` is stored in the schedule and its
     * execution resources are deducted.
     */
    pub fn choose_cycle(
        &mut self,
        node: &RcEq<Node>,
        life: &mut Life<Time>,
    ) {
        life.born = cmp::max(life.born, *self.pressure.latest_time_with_unused_register());
        while !self.fits(&*node, life.born.0) {
            life.born.0 += 1;
        }
        while self.cycles.len() <= life.born.0 {
            self.cycles.push(Cycle::new());
        }
        self.cycles[life.born.0].nodes.push(node.clone());
        self.cycles[life.born.0].available -= node.op.cost();
        let register = self.pressure
            .allocate_register(life.clone(), node.clone())
            .map(|(register, previous_node)| {
                if let Some(previous_node) = previous_node {
                    // Steal `register` from `previous_node`. Spill the latter.
                    let mut info = self.infos.get_mut(&previous_node).expect("missing NodeInfo");
                    assert_eq!(info.register, Some(register));
                    info.register = None;
                }
                register
            });
        self.infos.insert(node.clone(), NodeInfo {life: life.clone(), register});
    }
}
