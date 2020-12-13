use std::{cmp, fmt};
use std::collections::{HashMap};

use crate::util::{RcEq};
use super::dataflow::{Node, Op};
use super::pressure::{Life, Pressure};

// TODO: Move to architecture abstraction layer.
pub const PARALLELISM: usize = 3;

/** Records all information about one cycle of the schedule. */
#[derive(Debug)]
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

/**
 * Time is measured in cycles backwards from the end of the Schedule, and
 * instructions backwards within a cycle.
 */
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Time {
    cycle: cmp::Reverse<usize>,
    instruction: cmp::Reverse<usize>,
}

impl fmt::Debug for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_tuple("Time")
            .field(&self.cycle)
            .field(&self.instruction)
            .finish()
    }
}

impl std::ops::Sub<usize> for Time {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        if rhs == 0 {
            self
        } else {
            Time {
                cycle: cmp::Reverse(self.cycle.0 + rhs),
                instruction: cmp::Reverse(0),
            }
        }
    }
}

pub const EARLY: Time = Time {cycle: cmp::Reverse(usize::MAX), instruction: cmp::Reverse(0)};
pub const LATE: Time = Time {cycle: cmp::Reverse(0), instruction: cmp::Reverse(0)};

/**
 * Usage information about a Node in a WorkList. Information is collected
 * incrementally as references to the Node are processed.
 */
#[derive(Debug)]
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
#[derive(Debug)]
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
            let born = dies - latency;
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

#[derive(Debug)]
struct NodeInfo {
    /** The lifetime of the result of the Node. */
    life: Life<Time>,
    /** The logical register (if any) which will hold the result. */
    register: Option<usize>,
}

/** An instruction schedule. */
pub struct Schedule {
    /** The Cycles we're allocating, in reverse order: 0 is the last Cycle. */
    cycles: Vec<Cycle>,
    /** The Input Nodes, which are notionally at the beginning of time. */
    inputs: Vec<RcEq<Node>>,
    /** NodeInfo for every Node in the schedule. */
    infos: HashMap<RcEq<Node>, NodeInfo>,
    /** Register pressure as a function of time. */
    pressure: Pressure<Time, RcEq<Node>>,
}

impl fmt::Debug for Schedule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Schedule")
            .field("cycles", &self.cycles)
            .field("inputs", &self.inputs)
            .field("infos", &self.infos)
            .finish()
    }
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
            inputs: Vec::new(),
            infos: HashMap::new(),
            pressure: Pressure::new(|| LATE),
        };
        for &(ref node, time) in &roots {
            work_list.schedule(node, Life::new(time, time), &mut schedule);
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
     * as late as possible but no later than `life.born`. `node` is stored in
     * the Schedule and its execution resources are deducted. `life.born` is
     * set to the Time just before `node` in the Schedule; `life` will
     * therefore contain `node`.
     */
    pub fn choose_cycle(
        &mut self,
        node: &RcEq<Node>,
        life: &mut Life<Time>,
    ) {
        match node.op {
            Op::Input(_) => {
                life.born = EARLY;
                self.inputs.push(node.clone());
            },
            _ => {
                life.born = cmp::max(life.born, *self.pressure.latest_time_with_unused_register());
                while !self.fits(&*node, life.born.cycle.0) {
                    life.born.cycle.0 += 1;
                }
                while self.cycles.len() <= life.born.cycle.0 {
                    self.cycles.push(Cycle::new());
                }
                let mut cycle = &mut self.cycles[life.born.cycle.0];
                assert!(life.born.instruction.0 <= cycle.nodes.len());
                cycle.nodes.push(node.clone());
                life.born.instruction.0 = cycle.nodes.len();
                cycle.available -= node.op.cost();
            },
        }
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

    /** Yields the Input Nodes. */
    pub fn inputs<'a>(&'a self) -> impl 'a + Iterator<Item=(&'a RcEq<Node>, Life<Time>, Option<usize>)> {
        self.inputs.iter().map(move |node| {
            let info = self.infos.get(node).expect("missing NodeInfo");
            (node, info.life, info.register)
        })
    }

    /** Yields the Nodes in the order that we've decided to execute them. */
    pub fn iter<'a>(&'a self) -> impl 'a + Iterator<Item=(&'a RcEq<Node>, Life<Time>, Option<usize>)> {
        self.cycles.iter().rev().flat_map(|cycle| {
            cycle.nodes.iter().rev()
        }).map(move |node| {
            let info = self.infos.get(node).expect("missing NodeInfo");
            (node, info.life, info.register)
        })
    }
}
