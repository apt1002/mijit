use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Formatter};

use super::{NUM_REGISTERS, all_registers, Resources, Op, Dataflow, Node, Out};
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
    Spill(Out, Out),
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

/// The information that a [`Allocator`] stores about each [`Out`].
#[derive(Default)]
struct OutInfo {
    /// The `Time` at which the `Out` became available.
    time: Option<Time>,
    /// The `Register` allocated for the `Out`.
    reg: Option<Register>,
}

impl Debug for OutInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "OutInfo {{time: {:?}, reg: {:?}}}", self.time, self.reg)
    }
}

/// The information that an [`Allocator`] stores about each [`Register`].
#[derive(Default)]
struct RegInfo {
    /// The last `Time` at which the [`Register`] is used, or zero.
    time: Time,
    /// The contents of the `Register` at the current time.
    out: Option<Out>,
}

impl Debug for RegInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "RegInfo {{time: {:?}, out: {:?}}}", self.time, self.out)
    }
}

//-----------------------------------------------------------------------------

/// The state of the code generation algorithm. The state is mutated as
/// [`Instruction`]s are added, in the order specified by a [`Schedule`].
#[derive(Debug)]
struct Allocator<'a> {
    /// The dataflow graph.
    dataflow: &'a Dataflow,
    /// The concatenation of the `keep_alive` sets of all [`Node`]s remaining
    /// to be processed. Each call to `add_node()` pops a few `Out`s from this.
    usage: Usage<Out>,
    /// The [`Instruction`]s processed so far.
    placer: Placer<Instruction>,
    /// An `OutInfo` for each `Out`.
    outs: ArrayMap<Out, OutInfo>,
    /// The `Time` at which each [`Node`] was executed.
    node_times: ArrayMap<Node, Option<Time>>,
    /// A `RegInfo` for each `Reg`.
    regs: ArrayMap<Register, RegInfo>,
    /// The `Register` allocator state.
    pool: RegisterPool,
}

impl<'a> Allocator<'a> {
    /// Create a new `Allocator`.
    ///
    ///  - effects - [`Node`]s representing side-effects that have already
    ///  occurred.
    ///  - variables - A mapping from the live [`Out`]s to [`Variable`]s.
    ///  - dataflow - The data flow graph.
    ///  - usage - The suggested execution order and usage information.
    pub fn new(
        effects: &HashSet<Node>,
        variables: &HashMap<Out, Variable>,
        dataflow: &'a Dataflow,
        usage: Usage<Out>,
    ) -> Self {
        // Initialize the data structures with the live registers of `variables`.
        let mut dirty = ArrayMap::new(NUM_REGISTERS);
        let mut outs: ArrayMap<Out, OutInfo> = dataflow.out_map();
        let mut node_times: ArrayMap<Node, Option<Time>> = dataflow.node_map();
        for &node in effects {
            node_times[node] = Some(EARLY);
        }
        let mut regs: ArrayMap<Register, RegInfo> = ArrayMap::new(NUM_REGISTERS);
        for (&out, &value) in variables.iter() {
            if usage.topmost(&out).is_some() {
                if let Variable::Register(reg) = value {
                    dirty[reg] = true;
                    regs[reg].out = Some(out);
                    outs[out].reg = Some(reg);
                }
                outs[out].time = Some(EARLY);
            }
        }
        // Construct and return.
        Allocator {
            dataflow: dataflow,
            usage: usage,
            placer: Placer::new(),
            outs: outs,
            node_times: node_times,
            regs: regs,
            pool: RegisterPool::new(dirty),
        }
    }

    /// Returns the [`Register`] containing `out`, if any.
    fn current_reg(&self, out: Out) -> Option<Register> {
        self.outs[out].reg.filter(|&reg| self.regs[reg].out == Some(out))
    }

    /// Record that we used `reg` at `time` (either reading or writing).
    fn use_reg(&mut self, reg: Register, time: Time) {
        self.regs[reg].time.max_with(time);
    }

    /// Select a `Register` to spill and free it.
    fn free_a_register(&mut self) -> Register {
        let i = map_filter_max(all_registers(), |reg| {
            self.regs[reg].out
                .filter(|_| !self.pool.is_clean(reg))
                .map(|out| std::cmp::Reverse(
                    self.usage.topmost(&out).expect("Dirty register is unused")
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
            let out_x = self.regs[reg_x].out.unwrap();
            let out_y = self.regs[reg_y].out.unwrap();
            let mut time = self.outs[out_x].time.expect("Not computed yet");
            time.max_with(self.outs[out_y].time.expect("Not computed yet"));
            self.placer.add_item(Spill(out_x, out_y), SPILL_COST, &mut time);
            self.use_reg(reg_x, time);
            self.use_reg(reg_y, time);
        }
    }

    /// Called for each [`Node`] in forwards order.
    /// - `num_keep_alives` - the number of `Out`s which must survive until
    ///   after `Node` has been executed. This many items will be popped from
    ///   `self.usage`. These `Out`s are often just the inputs of `node`, but
    ///   can also include e.g. values needed by `node`'s cold paths.
    pub fn add_node(&mut self, node: Node, num_keep_alives: usize) {
        println!("add_node({:?}, {:?})", node, num_keep_alives);
        let df: &'a Dataflow = self.dataflow;
        let mut time = EARLY; // Earliest time (in cycles) when we can place `node`.
        // Free every input `Register` that won't be used again.
        let keep_alives: Vec<Out> = (0..num_keep_alives).map(|_| {
            let in_ = self.usage.pop().expect("Incorrect usage information");
            if self.usage.topmost(&in_).is_none() {
                // This can happen at most once for each distinct `in_`.
                if let Some(reg) = self.current_reg(in_) {
                    self.pool.free(reg);
                }
            }
            in_
        }).collect();
        println!("keep_alives = {:?}", keep_alives);
        // Spill until we have enough registers to hold the outputs of `node`.
        self.spill_until(df.num_outs(node));
        // Bump `time` until the dependencies are available.
        for &dep in df.deps(node) {
            time.max_with(self.node_times[dep].expect("Not executed yet"));
        }
        // Bump `time` until the operands are available.
        for (&in_, &latency) in df.ins(node).iter().zip(df.cost(node).input_latencies) {
            println!("{:?} was written at time {:?} with latency {:?}", in_, self.outs[in_].time, latency);
            time.max_with(self.outs[in_].time.expect("Not computed yet") + latency as usize);
        }
        // Bump `time` until some destination registers are available.
        for out in df.outs(node) {
            let reg = self.pool.allocate();
            self.outs[out].reg = Some(reg);
            println!("{:?} becomes available at time {:?}", reg, self.regs[reg].time);
            time.max_with(self.regs[reg].time);
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if df.ins(node).iter().any(|&in_| self.current_reg(in_).is_none()) {
            // We can't be sure it's not still in a `Register`; this is a guess.
            resources += SLOT_COST;
        }
        // FIXME: A long series of zero-cost nodes will crash the placer.
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times[node] = Some(time);
        // Record when the inputs were used.
        for in_ in keep_alives {
            println!("Keep-alive {:?} is currently in {:?}", in_, self.current_reg(in_));
            if let Some(reg) = self.current_reg(in_) {
                println!("Marking it as used at time {:?}", time);
                self.use_reg(reg, time);
            }
        }
        // Record when the outputs become available.
        for (out, &latency) in df.outs(node).zip(df.cost(node).output_latencies) {
            println!("Marking {:?} as written at time {:?} with latency {:?}", out, time, latency);
            self.regs[self.outs[out].reg.unwrap()] = RegInfo {time: time, out: Some(out)};
            self.outs[out].time = Some(time + latency as usize);
        }
    }

    /// Returns the finished [`Instruction`] order and [`Register`] allocation.
    pub fn finish(self) -> (Vec<Instruction>, ArrayMap<Out, Option<Register>>) {
        let instructions: Vec<_> = self.placer.iter().cloned().collect();
        let allocation = self.outs.iter().map(|info| info.reg).collect();
        (instructions, allocation)
    }
}

/// Choose the execution order and allocate [`Register`]s.
///
/// - effects - [`Node`]s representing side-effects that have already occurred.
/// - variables - the [`Variable`]s passed on entry to the hot path.
/// - dataflow - the dataflow graph.
/// - nodes - the [`Node`]s that need to be executed on the hot path,
///   topologically sorted. Includes the exit node.
/// - get_keep_alives - for [`Op::Guard`] `Node`s, returns the dataflow
///   dependencies of the cold paths.
///
/// Returns:
/// - instructions - the execution order. Excludes the exit node.
/// - allocation - which `Register` each `Out` should be computed into.
pub fn allocate<'a>(
    effects: &HashSet<Node>,
    variables: &HashMap<Out, Variable>,
    dataflow: &Dataflow,
    nodes: &[Node],
    get_keep_alives: impl Fn(Node) -> Option<&'a HashSet<Out>>,
) -> (
    Vec<Instruction>,
    ArrayMap<Out, Option<Register>>
) {
    // Reverse `nodes` and compute the `Out`s each one uses.
    let mut usage = Usage::default();
    let mut nodes_rev: Vec<(Node, usize)> = nodes.iter().rev().map(|&node| {
        let mut keep_alives: Vec<Out> = dataflow.ins(node).iter().copied().collect();
        if let Some(ins) = get_keep_alives(node) { keep_alives.extend(ins); }
        for &in_ in &keep_alives { usage.push(in_); }
        println!("Keep-alives for {:?} are {:?}", node, keep_alives);
        (node, keep_alives.len())
    }).collect();
    // Schedule and allocate registers for every `Node`s except the exit node.
    let mut a = Allocator::new(effects, variables, dataflow, usage);
    while let Some((node, num_keep_alives)) = nodes_rev.pop() {
        if !matches!(dataflow.op(node), Op::Convention) {
            a.add_node(node, num_keep_alives);
        } else {
            // Exit node should be last.
            assert_eq!(a.usage.len(), num_keep_alives);
        }
    }
    a.finish()
}
