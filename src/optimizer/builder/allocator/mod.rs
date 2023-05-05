use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Formatter};

use super::{dep, NUM_REGISTERS, all_registers, Resources, Dep, Dataflow, Node, Frontier};
use super::cost::{BUDGET, SPILL_COST, SLOT_COST};
use super::code::{Register, Variable};
use crate::util::{ArrayMap, map_filter_max, Usage};

mod pool;
use pool::{RegisterPool};

mod placer;
use placer::{Time, LEAST as EARLY, Placer};

//-----------------------------------------------------------------------------

#[derive(Copy, Clone, PartialEq)]
pub enum Instruction {
    Spill(Node, Node),
    Node(Node),
}

use Instruction::*;

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            Spill(out_x, out_y) => write!(f, "({:?}, {:?})", out_x, out_y),
            Node(node) => node.fmt(f),
        }
    }
}

//-----------------------------------------------------------------------------

/// The state of the code generation algorithm. The state is mutated as
/// [`Instruction`]s are added.
#[derive(Debug)]
struct Allocator<'a> {
    /// The dataflow graph.
    dataflow: &'a Dataflow,
    /// The concatenation of the `input` lists of all [`Node`]s remaining
    /// to be processed. Each call to `add_node()` pops some `Node`s from this.
    usage: Usage<Node>,
    /// A [`Dep`] for each item in `usage`.
    deps: Vec<Dep>,
    /// The [`Instruction`]s processed so far.
    placer: Placer<Instruction>,
    /// The `Register` allocated for each `Node`'s result, if any.
    allocation: HashMap<Node, Register>,
    /// The `Time` at which each `Node`'s result was last accessed.
    read_times: HashMap<Node, Time>,
    /// The `Time` at which each `Node`'s result became available.
    write_times: HashMap<Node, Time>,
    /// The `Time` at which each `Node` was executed.
    node_times: HashMap<Node, Time>,
    /// The contents of each [`Register`] at the current time.
    regs: ArrayMap<Register, Option<Node>>,
    /// The `Register` allocator state.
    pool: RegisterPool,
}

impl<'a> Allocator<'a> {
    /// Create a new `Allocator`.
    ///
    /// - effects - [`Node`]s representing side-effects that have already
    ///   occurred.
    /// - variables - A mapping from the live [`Node`]s to [`Variable`]s.
    /// - dataflow - The data flow graph.
    /// - usage - The concatenation of the `input` lists of all `Node`s that
    ///   will be processed.
    /// - deps - A [`Dep`] for each item in `usage`.
    pub fn new(
        effects: &HashSet<Node>,
        variables: &HashMap<Node, Variable>,
        dataflow: &'a Dataflow,
        usage: Usage<Node>,
        deps: Vec<Dep>,
    ) -> Self {
        // Initialize the data structures with the live registers of `variables`.
        let mut dirty = ArrayMap::new(NUM_REGISTERS);
        let mut allocation: HashMap<Node, Register> = HashMap::new();
        let mut write_times: HashMap<Node, Time> = HashMap::new();
        let mut node_times: HashMap<Node, Time> = HashMap::new();
        for &node in effects {
            node_times.insert(node, EARLY);
        }
        let mut regs: ArrayMap<Register, Option<Node>> = ArrayMap::new(NUM_REGISTERS);
        for (&node, &value) in variables.iter() {
            if usage.topmost(&node).is_some() {
                // `node` is alive on entry.
                if let Variable::Register(reg) = value {
                    dirty[reg] = true;
                    regs[reg] = Some(node);
                    allocation.insert(node, reg);
                }
                write_times.insert(node, EARLY);
            }
        }
        // Construct and return.
        let placer = Placer::new();
        let read_times: HashMap<Node, Time> = HashMap::new();
        let pool = RegisterPool::new(dirty);
        Allocator {dataflow, usage, deps, placer, allocation, read_times, write_times, node_times, regs, pool}
    }

    /// Returns the [`Register`] containing `node`, if any.
    fn current_reg(&self, node: Node) -> Option<Register> {
        self.allocation.get(&node).copied().filter(
            |&reg| self.regs[reg] == Some(node)
        )
    }

    /// Pop one [`Node`] from `self.usage` and one `dep` from `self.deps`.
    /// Frees its [`Register`], if any, if the `Node` has no remaining uses.
    fn pop_use(&mut self) -> (Node, Dep) {
        let node = self.usage.pop().expect("Incorrect usage information");
        let dep = self.deps.pop().expect("Incorrect dependency information");
        if self.usage.topmost(&node).is_none() {
            if let Some(reg) = self.current_reg(node) {
                self.pool.free(reg);
            }
        }
        (node, dep)
    }

    /// Record that we accessed `node` at `time` (either reading or writing).
    fn access(&mut self, node: Node, time: Time) {
        self.read_times.entry(node).or_insert(EARLY).max_with(time);
    }

    /// Select a `Register` to spill and free it.
    fn free_a_register(&mut self) -> Register {
        let i = map_filter_max(all_registers(), |reg| {
            self.regs[reg]
                .filter(|_| !self.pool.is_clean(reg))
                .map(|node| std::cmp::Reverse(
                    self.usage.topmost(&node).expect("Dirty register is unused")
                ))
        }).expect("No register is dirty");
        let reg = Register::new(i as u8).unwrap();
        self.pool.free(reg);
        reg
    }

    /// Spills values until at least `num_required` registers are free.
    fn spill_until(&mut self, num_required: usize) {
        while self.pool.num_clean() < num_required {
            let reg_x = self.free_a_register();
            let reg_y = self.free_a_register();
            // Spill the `Register`.
            let out_x = self.regs[reg_x].unwrap();
            let out_y = self.regs[reg_y].unwrap();
            let mut time = self.write_times[&out_x];
            time.max_with(self.write_times[&out_y]);
            self.placer.add_item(Spill(out_x, out_y), SPILL_COST, &mut time);
            self.access(out_x, time);
            self.access(out_y, time);
        }
    }

    /// Called for each [`Node`] in forwards order.
    /// - `num_inputs` - a [`Dep`] for each input of `node`. For each one, a
    /// `Node` will be popped from `self.usage` and a [`Dep`] from `self.deps`.
    /// These `Node`s are often just the inputs of `node`, but can also include
    /// e.g. values needed by `node`'s cold paths.
    pub fn add_node(&mut self, node: Node, num_inputs: usize) {
        let df: &'a Dataflow = self.dataflow;
        let mut time = EARLY; // Earliest time (in cycles) when we can place `node`.
        // Read inputs.
        // Check for spilled inputs.
        // Free every input `Register` that won't be used again.
        // Bump `time` until the inputs are available.
        let mut inputs = Vec::<(Node, Dep)>::new();
        let mut has_spilled_input = false;
        for _ in 0..num_inputs {
            let (in_, dep) = self.pop_use();
            inputs.push((in_, dep));
            if !dep.is_cold() {
                if dep.is_value() {
                    let latency = 1; // TODO.
                    time.max_with(self.write_times[&in_] + latency as usize);
                    has_spilled_input |= self.current_reg(in_).is_none();
                } else {
                    time.max_with(self.node_times[&in_]);
                }
            }
        }
        // Bump `time` until a destination register is available.
        if df.has_out(node) {
            self.spill_until(1);
            let reg = self.pool.allocate();
            self.allocation.insert(node, reg);
            if let Some(prev) = self.regs[reg].replace(node) {
                // `reg` was previously used to hold `prev`.
                if let Some(&read_time) = self.read_times.get(&prev) {
                    // `prev` was last accessed at `read_time`.
                    time.max_with(read_time);
                }
            }
            if self.usage.topmost(&node).is_none() {
                // `node` will never be used again. Free `reg` immediately.
                self.pool.free(reg);
            }
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if has_spilled_input {
            // We can't be sure it's not still in a `Register`; this is a guess.
            resources += SLOT_COST;
        }
        // FIXME: A long series of zero-cost nodes will crash the placer.
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times.insert(node, time);
        // Record when the inputs were used.
        for &(in_, dep) in &inputs {
            if dep.is_value() {
                self.access(in_, time);
            }
        }
        // Record when the output becomes available.
        if let Some(ol) = df.cost(node).output_latency {
            self.access(node, time);
            self.write_times.insert(node, time + ol as usize);
        }
    }

    /// Read the [`Node`]s that are live on exit.
    fn finish(mut self, num_outputs: usize) -> (Vec<Instruction>, HashMap<Node, Register>) {
        for _ in 0..num_outputs { let _ = self.pop_use(); }
        assert_eq!(self.usage.len(), 0);
        assert_eq!(self.deps.len(), 0);
        assert!(all_registers().all(|reg| self.pool.is_clean(reg)));
        (self.placer.iter().cloned().collect(), self.allocation)
    }
}

/// Choose the execution order and allocate [`Register`]s.
///
/// - effects - [`Node`]s representing side-effects that have already occurred.
/// - variables - the [`Variable`]s passed on entry to the hot path.
/// - dataflow - the dataflow graph.
/// - nodes - the [`Node`]s that need to be executed on the hot path,
///   topologically sorted.
/// - get_frontier - for [`Guard`] `Node`s, returns the dependencies of the
///   cold paths.
/// - outputs - the [`Node`]s that are live on exit.
///
/// Returns:
/// - instructions - the execution order.
/// - allocation - which `Register` holds each `Node`'s result.
///
/// [`Guard`]: super::Op::Guard
// FIXME: Place `Send(x, y)` and `Store(y)` after all `Load(y)`s.
pub fn allocate<'a>(
    effects: &HashSet<Node>,
    variables: &HashMap<Node, Variable>,
    dataflow: &Dataflow,
    nodes: &[Node],
    get_frontier: impl Fn(Node) -> Option<&'a Frontier>,
    outputs: &[Node],
) -> (
    Vec<Instruction>,
    HashMap<Node, Register>
) {
    // Reverse `nodes` and compute their inputs.
    let mut usage = Usage::default();
    let mut deps = Vec::new();
    for &node in outputs {
        usage.push(node);
        deps.push(Dep::VALUE);
    }
    let mut nodes_rev: Vec<(Node, usize)> = nodes.iter().rev().map(|&node| {
        let start = usage.len();
        assert_eq!(start, deps.len());
        dataflow.each_input(node, |in_, dep| {
            usage.push(in_);
            deps.push(dep);
        });
        if let Some(f) = get_frontier(node) {
            for (&in_, &v) in &f.0 {
                usage.push(in_);
                deps.push(Dep(v, dep::Effect::Cold));
            }
        }
        let end = usage.len();
        assert_eq!(end, deps.len());
        (node, end - start)
    }).collect();
    // Schedule and allocate registers for every `Node`.
    let mut a = Allocator::new(effects, variables, dataflow, usage, deps);
    while let Some((node, num_inputs)) = nodes_rev.pop() {
        a.add_node(node, num_inputs);
    }
    a.finish(outputs.len())
}
