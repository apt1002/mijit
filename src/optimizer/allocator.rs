use std::fmt::{self, Debug, Formatter};

use super::{NUM_REGISTERS, all_registers, Schedule, RegisterPool};
use super::dataflow::{Dataflow, Node, Out};
use super::cost::{SPILL_COST, SLOT_COST};
use super::placer::{Time, LEAST as EARLY, Placer};
use super::code::{Register, Variable, Convention};
use crate::util::{ArrayMap, map_filter_max};

//-----------------------------------------------------------------------------

#[derive(Copy, Clone)]
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

/** The information that a [`Allocator`] stores about each [`Out`]. */
#[derive(Default)]
struct OutInfo {
    /** The `Time` at which the `Out` became available. */
    time: Option<Time>,
    /** The `Register` allocated for the `Out`. */
    reg: Option<Register>,
}

impl Debug for OutInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "OutInfo {{time: {:?}, reg: {:?}}}", self.time, self.reg)
    }
}

/** The information that an [`Allocator`] stores about each [`Register`]. */
#[derive(Default)]
struct RegInfo {
    /** The last `Time` at which the [`Register`] is used, or zero. */
    time: Time,
    /** The contents of the `Register` at the current time. */
    out: Option<Out>,
}

impl Debug for RegInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "RegInfo {{time: {:?}, out: {:?}}}", self.time, self.out)
    }
}

//-----------------------------------------------------------------------------

/**
 * The state of the code generation algorithm. The state is mutated as
 * [`Instruction`]s are added, in the order specified by a [`Schedule`].
 */
#[derive(Debug)]
struct Allocator<'a> {
    /** The [`Node`]s remaining to be processed. */
    schedule: Schedule<'a>,
    /** The [`Instruction`]s processed so far. */
    placer: Placer<Instruction>,
    /** An `OutInfo` for each `Out`. */
    outs: ArrayMap<Out, OutInfo>,
    /** The `Time` at which each [`Node`] was executed. */
    node_times: ArrayMap<Node, Option<Time>>,
    /** A `RegInfo` for each `Reg`. */
    regs: ArrayMap<Register, RegInfo>,
    /** The `Register` allocator state. */
    pool: RegisterPool,
}

impl<'a> Allocator<'a> {
    pub fn new(before: &'a Convention, schedule: Schedule<'a>) -> Self {
        let df: &'a Dataflow = schedule.dataflow;
        // Initialize the data structures with the live registers of `before`.
        let mut dirty = ArrayMap::new(NUM_REGISTERS);
        let mut outs: ArrayMap<Out, OutInfo> = df.out_map();
        let mut node_times: ArrayMap<Node, Option<Time>> = df.node_map();
        node_times[df.entry_node()] = Some(EARLY);
        let mut regs: ArrayMap<Register, RegInfo> = ArrayMap::new(NUM_REGISTERS);
        for (out, &value) in df.outs(df.entry_node()).zip(&*before.live_values) {
            if schedule.first_use(out).is_some() {
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
            schedule: schedule,
            placer: Placer::new(),
            outs: outs,
            node_times: node_times,
            regs: regs,
            pool: RegisterPool::new(dirty),
        }
    }

    /** Returns the [`Register`] containing `out`, if any. */
    fn current_reg(&self, out: Out) -> Option<Register> {
        self.outs[out].reg.filter(|&reg| self.regs[reg].out == Some(out))
    }

    /** Record that we used `reg` at `time` (either reading or writing). */
    fn use_reg(&mut self, reg: Register, time: Time) {
        self.regs[reg].time.max_with(time);
    }

    /** Select a `Register` to spill and free it. */
    fn free_a_register(&mut self) -> Register {
        let i = map_filter_max(all_registers(), |reg| {
            self.regs[reg].out
                .filter(|_| !self.pool.is_clean(reg))
                .map(|out| self.schedule.first_use(out))
                .map(std::cmp::Reverse)
        });
        let reg = Register::new(i.expect("No register is dirty") as u8).unwrap();
        self.pool.free(reg);
        reg
    }

    /** Spills values until at least `num_required` registers are free. */
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

    /** Called for each [`Node`] in the [`Schedule`] in forwards order. */
    pub fn add_node(&mut self, node: Node) {
        let df: &'a Dataflow = self.schedule.dataflow;
        let mut time = EARLY; // Earliest time (in cycles) when we can place `node`.
        // Free every input `Register` that won't be used again.
        for &in_ in df.ins(node) {
            if self.schedule.first_use(in_).is_none() {
                if let Some(reg) = self.current_reg(in_) {
                    self.pool.free(reg);
                }
            }
        }
        // Spill until we have enough registers to hold the outputs of `node`.
        self.spill_until(df.num_outs(node));
        // Bump `time` until the dependencies are available.
        for &dep in df.deps(node) {
            time.max_with(self.node_times[dep].expect("Not executed yet"));
        }
        // Bump `time` until the operands are available.
        for (&in_, &latency) in df.ins(node).iter().zip(df.cost(node).input_latencies) {
            time.max_with(self.outs[in_].time.expect("Not computed yet") + latency as usize);
        }
        // Bump `time` until some destination registers are available.
        for out in df.outs(node) {
            let reg = self.pool.allocate();
            self.outs[out].reg = Some(reg);
            time.max_with(self.regs[reg].time);
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if df.ins(node).iter().any(|&in_| self.current_reg(in_).is_none()) {
            // We can't be sure it's not still in a `Register`; this is a guess.
            resources += SLOT_COST;
        }
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times[node] = Some(time);
        // Record when the inputs were used.
        for &in_ in df.ins(node) {
            if let Some(reg) = self.current_reg(in_) {
                self.use_reg(reg, time);
            }
        }
        // Record when the outputs become available.
        for (out, &latency) in df.outs(node).zip(df.cost(node).output_latencies) {
            self.regs[self.outs[out].reg.unwrap()] = RegInfo {time: time, out: Some(out)};
            self.outs[out].time = Some(time + latency as usize);
        }
    }

    /**
     * Returns the finished [`Instruction`] order and [`Register`] allocation.
     * Also returns a [`Register`] that is unused at the end of the code.
     */
    pub fn finish(self) -> (Vec<Instruction>, ArrayMap<Out, Option<Register>>) {
        let instructions: Vec<_> = self.placer.iter().cloned().collect();
        let allocation = self.outs.iter().map(|info| info.reg).collect();
        (instructions, allocation)
    }
}

impl<'a> std::iter::Iterator for Allocator<'a> {
    type Item = Node;

    fn next(&mut self) -> Option<Self::Item> { self.schedule.next() }

    fn size_hint(&self) -> (usize, Option<usize>) { self.schedule.size_hint() }
}

/** Choose the execution order and allocate [`Register`]s. */
pub fn allocate(before: &Convention, schedule: Schedule) -> (
    Vec<Instruction>,
    ArrayMap<Out, Option<Register>>
) {
    let mut a = Allocator::new(before, schedule);
    while let Some(node) = a.next() {
        a.add_node(node);
    }
    a.finish()
}
