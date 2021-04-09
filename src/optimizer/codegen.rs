use std::cmp::{max};
use std::collections::{HashMap};
use std::fmt::{self, Debug, Formatter};

use super::{Convention, NUM_REGISTERS, all_registers, Op, Schedule, RegisterPool, Placer, moves};
use super::dataflow::{Dataflow, Node, Out};
use super::cost::{SPILL_COST, SLOT_COST};
use super::code::{Register, Slot, Value, Action};
use crate::util::{ArrayMap, map_filter_max};

//-----------------------------------------------------------------------------

#[derive(Copy, Clone)]
enum Instruction {
    Absent,
    Spill(Out),
    Node(Node),
}

use Instruction::*;

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self {
            &Absent => write!(f, "Absent"),
            &Spill(out) => out.fmt(f),
            &Node(node) => node.fmt(f),
        }
    }
}

impl Default for Instruction {
    fn default() -> Self {
        Absent
    }
}

//-----------------------------------------------------------------------------

/** The information that a [`CodeGen`] stores about each [`Out`]. */
pub struct OutInfo {
    /** The time at which the `Out` became available, or [`usize::MAX`]. */
    time: usize,
    /** The `Register` allocated for the `Out`. */
    reg: Option<Register>,
}

impl Debug for OutInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "OutInfo {{time: {:?}, reg: {:?}}}", self.time, self.reg)
    }
}

impl Default for OutInfo {
    fn default() -> Self {
        OutInfo {
            time: usize::MAX,
            reg: None,
        }
    }
}

/** The information that a [`CodeGen`] stores about each [`Register`]. */
#[derive(Default)]
pub struct RegInfo {
    /** The last time at which each [`Register`] is used, or zero. */
    time: usize,
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
 * [`Instructions`] are added, in the order specified by a [`Schedule`].
 */
#[derive(Debug)]
struct CodeGen<'a> {
    /** The [`Convention`] used on entry. */
    before: &'a Convention,
    /** The [`Convention`] used on exit. */
    after: &'a Convention,
    /** The [`Node`]s remaining to be processed. */
    schedule: Schedule<'a>,
    /** The [`Instruction`]s processed so far. */
    placer: Placer<Instruction>,
    /** An `OutInfo` for each `Out`. */
    outs: ArrayMap<Out, OutInfo>,
    /** The time at which each [`Node`] was executed. */
    node_times: ArrayMap<Node, usize>,
    /** A `RegInfo` for each `Reg`. */
    regs: ArrayMap<Register, RegInfo>,
    /** The `Register` allocator state. */
    pool: RegisterPool,
}

impl<'a> CodeGen<'a> {
    pub fn new(before: &'a Convention, after: &'a Convention, schedule: Schedule<'a>) -> Self {
        let df: &'a Dataflow = schedule.dataflow;
        // Initialize the data structures with the live registers of `before`.
        let mut dirty = ArrayMap::new(NUM_REGISTERS);
        let mut outs: ArrayMap<Out, OutInfo> = df.out_map();
        let mut regs: ArrayMap<Register, RegInfo> = ArrayMap::new(NUM_REGISTERS);
        for (out, &value) in df.outs(df.entry_node()).zip(&before.live_values) {
            if schedule.first_use(out).is_some() {
                match value {
                    Value::Register(reg) => {
                        dirty[reg] = true;
                        regs[reg].out = Some(out);
                        outs[out].reg = Some(reg);
                    },
                    Value::Slot(_) => {},
                }
                outs[out].time = 0;
            }
        }
        // Construct and return.
        let cg = CodeGen {
            before: before,
            after: after,
            schedule: schedule,
            placer: Placer::new(),
            outs: outs,
            node_times: df.node_map(),
            regs: regs,
            pool: RegisterPool::new(dirty),
        };
        cg
    }

    /** Returns the [`Register`] containing `out`, if any. */
    fn current_reg(&self, out: Out) -> Option<Register> {
        self.outs[out].reg.filter(|&reg| self.regs[reg].out == Some(out))
    }

    /** Record that we used `reg` at `time` (either reading or writing). */
    fn use_reg(&mut self, reg: Register, time: usize) {
        self.regs[reg].time = max(self.regs[reg].time, time);
    }

    /** Spills values until at least `num_required` registers are free. */
    fn spill_until(&mut self, num_required: usize) {
        while self.pool.num_clean() < num_required {
            // Select a `Register` to spill.
            let i = map_filter_max(all_registers(), |reg| {
                self.regs[reg].out
                    .filter(|_| !self.pool.is_clean(reg))
                    .map(|out| self.schedule.first_use(out))
                    .map(std::cmp::Reverse)
            });
            let reg = Register::new(i.expect("No register is dirty") as u8).unwrap();
            // Spill the `Register`.
            let out = self.regs[reg].out.unwrap();
            let mut time = self.outs[out].time;
            self.placer.add_item(Spill(out), SPILL_COST, &mut time);
            self.use_reg(reg, time);
            // Free the `Register`.
            self.pool.free(reg);
        }
    }

    /** Called for each [`Node`] in the [`Schedule`] in forwards order. */
    pub fn add_node(&mut self, node: Node) {
        let df: &'a Dataflow = self.schedule.dataflow;
        let mut time = 0; // Earliest time (in cycles) when we can place `node`.
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
            time = max(time, self.node_times[dep]);
        }
        // Bump `time` until the operands are available.
        for (&in_, &latency) in df.ins(node).iter().zip(df.cost(node).input_latencies) {
            time = max(time, self.outs[in_].time + latency as usize);
        }
        // Bump `time` until some destination registers are available.
        for out in df.outs(node) {
            let reg = self.pool.allocate();
            self.outs[out].reg = Some(reg);
            time = max(time, self.regs[reg].time);
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if df.ins(node).iter().any(|&in_| self.current_reg(in_).is_none()) {
            // We can't be sure it's not still in a `Register`; this is a guess.
            resources += SLOT_COST;
        }
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times[node] = time;
        // Record when the inputs were used.
        for &in_ in df.ins(node) {
            if let Some(reg) = self.current_reg(in_) {
                self.use_reg(reg, time);
            }
        }
        // Record when the outputs become available.
        for (out, &latency) in df.outs(node).zip(df.cost(node).output_latencies) {
            self.regs[self.outs[out].reg.unwrap()] = RegInfo {time: time, out: Some(out)};
            self.outs[out].time = time + latency as usize;
        }
    }

    /**
     * Allocate spill slots, resolve operands, convert all instructions to
     * [`Action`]s, and return them in the order they should be executed in.
     */
    pub fn finish(self, exit_node: Node) -> Box<[Action]> {
        let df: &'a Dataflow = self.schedule.dataflow;
        // Initialise bindings.
        let mut num_slots = self.before.slots_used;
        let mut spills: ArrayMap<Out, Option<Slot>> = df.out_map();
        let mut regs: ArrayMap<Register, Option<Out>> = ArrayMap::new(NUM_REGISTERS);
        for (out, &value) in df.outs(df.entry_node()).zip(&self.before.live_values) {
            match value {
                Value::Register(reg) => {
                    regs[reg] = Some(out);
                },
                Value::Slot(s) => {
                    assert!(s.0 < num_slots);
                    spills[out] = Some(s);
                },
            }
        }
        // Build the list of instructions.
        let mut ins: Vec<Value> = Vec::new(); // Temporary workspace.
        let mut outs: Vec<Register> = Vec::new(); // Temporary workspace.
        let mut ret: Vec<_> = self.placer.iter().map(|instruction| {
            ins.clear();
            outs.clear();
            match instruction {
                &Absent => panic!("Absent instruction"),
                &Spill(out) => {
                    assert!(spills[out].is_none()); // Not yet spilled.
                    let reg = self.outs[out].reg.expect("Spilled a non-register");
                    assert!(regs[reg] == Some(out)); // Not yet overwritten.
                    let slot = Slot(num_slots);
                    num_slots += 1;
                    spills[out] = Some(slot);
                    Action::Move(slot.into(), reg.into())
                },
                &Node(n) => {
                    ins.extend(df.ins(n).iter().map(|&in_| {
                        match self.outs[in_].reg.filter(|&reg| regs[reg] == Some(in_)) {
                            Some(reg) => Value::from(reg),
                            None => Value::from(spills[in_]
                                .expect("Value was overwritten but not spilled")
                            ),
                        }
                    }));
                    outs.extend(df.outs(n).map(|out| {
                        let reg = self.outs[out].reg.expect("Wrote a non-register");
                        regs[reg] = Some(out);
                        reg
                    }));
                    Op::to_action(df.op(n), &outs, &ins)
                },
            }
        }).collect();
        // Work out which live values need to be moved where.
        let mut is_used = ArrayMap::new(NUM_REGISTERS);
        let dest_to_src: HashMap<Value, Value> =
            df.ins(exit_node).iter().zip(&self.after.live_values).map(|(&out, &dest)| {
                let src = match self.outs[out].reg.filter(|&reg| regs[reg] == Some(out)) {
                    Some(reg) => reg.into(),
                    None => spills[out]
                        .expect("Value was overwritten but not spilled")
                        .into(),
                };
                if let Value::Register(r) = dest { is_used[r] = true; }
                if let Value::Register(r) = src { is_used[r] = true; }
                (dest, src)
            }).collect();
        // Allocate a temporary `Value` that is not live.
        // Use a `Register` if possible, otherwise allocate a `Slot`.
        let temp_reg: Value = all_registers()
            .find(|&r| !is_used[r])
            .map(Value::from)
            .unwrap_or_else(|| {
                let slot = Slot(num_slots);
                num_slots += 1;
                slot.into()
            });
        // Move all live values into the expected `Value`s.
        // TODO: Find a way to schedule these `Move`s properly or to eliminate them.
        ret.extend(moves(dest_to_src, temp_reg).map(|(dest, src)| Action::Move(dest, src)));
        // Return.
        ret.into()
    }
}

pub fn codegen(before: &Convention, after: &Convention, schedule: Schedule, exit_node: Node) -> Box<[Action]> {
    let mut codegen = CodeGen::new(before, after, schedule);
    while let Some(node) = codegen.schedule.next() {
        codegen.add_node(node);
    }
    codegen.finish(exit_node)
}
