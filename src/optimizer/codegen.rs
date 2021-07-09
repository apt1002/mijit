use std::collections::{HashMap};
use std::fmt::{self, Debug, Formatter};

use super::{Convention, NUM_REGISTERS, all_registers, Op, Schedule, RegisterPool, moves};
use super::dataflow::{Dataflow, Node, Out};
use super::cost::{SPILL_COST, SLOT_COST};
use super::placer::{Time, LEAST as EARLY, Placer};
use super::code::{Register, REGISTERS, Slot, Value, Action};
use crate::util::{ArrayMap, map_filter_max};

//-----------------------------------------------------------------------------

#[derive(Copy, Clone)]
enum Instruction {
    Absent,
    Spill(Out, Out),
    Node(Node),
}

use Instruction::*;

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            Absent => write!(f, "Absent"),
            Spill(out_x, out_y) => write!(f, "({:?}, {:?})", out_x, out_y),
            Node(node) => node.fmt(f),
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
#[derive(Default)]
pub struct OutInfo {
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

/** The information that a [`CodeGen`] stores about each [`Register`]. */
#[derive(Default)]
pub struct RegInfo {
    /** The last `Time` at which each [`Register`] is used, or zero. */
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
struct CodeGen<'a> {
    /** The number of global [`Slot`]s. */
    num_globals: usize,
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
    /** The `Time` at which each [`Node`] was executed. */
    node_times: ArrayMap<Node, Option<Time>>,
    /** A `RegInfo` for each `Reg`. */
    regs: ArrayMap<Register, RegInfo>,
    /** The `Register` allocator state. */
    pool: RegisterPool,
}

impl<'a> CodeGen<'a> {
    pub fn new(num_globals: usize, before: &'a Convention, after: &'a Convention, schedule: Schedule<'a>) -> Self {
        let df: &'a Dataflow = schedule.dataflow;
        // Initialize the data structures with the live registers of `before`.
        let mut dirty = ArrayMap::new(NUM_REGISTERS);
        let mut outs: ArrayMap<Out, OutInfo> = df.out_map();
        let mut node_times: ArrayMap<Node, Option<Time>> = df.node_map();
        node_times[df.entry_node()] = Some(EARLY);
        let mut regs: ArrayMap<Register, RegInfo> = ArrayMap::new(NUM_REGISTERS);
        for (out, &value) in df.outs(df.entry_node()).zip(&before.live_values) {
            if schedule.first_use(out).is_some() {
                if let Value::Register(reg) = value {
                    dirty[reg] = true;
                    regs[reg].out = Some(out);
                    outs[out].reg = Some(reg);
                }
                outs[out].time = Some(EARLY);
            }
        }
        // Construct and return.
        CodeGen {
            num_globals: num_globals,
            before: before,
            after: after,
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
            let mut time  = self.outs[out_x].time.expect("Not computed yet");
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
     * Allocate spill slots, resolve operands, convert all instructions to
     * [`Action`]s, and return them in the order they should be executed in.
     */
    pub fn finish(self, exit_node: Node) -> Box<[Action]> {
        let df: &'a Dataflow = self.schedule.dataflow;
        // Initialise bindings.
        let mut slots_used = self.before.slots_used;
        let mut spills: ArrayMap<Out, Option<Value>> = df.out_map();
        let mut regs: ArrayMap<Register, Option<Out>> = ArrayMap::new(NUM_REGISTERS);
        for (out, &value) in df.outs(df.entry_node()).zip(&self.before.live_values) {
            match value {
                Value::Register(r) => regs[r] = Some(out),
                Value::Global(g) => assert!(g.0 < self.num_globals),
                Value::Slot(s) => assert!(s.0 < slots_used),
            }
            spills[out] = Some(value);
        }
        // Build the list of instructions.
        let mut ins: Vec<Value> = Vec::new(); // Temporary workspace.
        let mut outs: Vec<Register> = Vec::new(); // Temporary workspace.
        let mut ret: Vec<Action> = Vec::new();
        for instruction in self.placer.iter() {
            ins.clear();
            outs.clear();
            ret.push(match *instruction {
                Absent => panic!("Absent instruction"),
                Spill(out_x, out_y) => {
                    assert!(spills[out_x].is_none()); // Not yet spilled.
                    let r_x = self.outs[out_x].reg.expect("Spilled a non-register");
                    assert!(regs[r_x] == Some(out_x)); // Not yet overwritten.
                    spills[out_x] = Some(Slot(slots_used).into());
                    slots_used += 1;

                    assert!(spills[out_y].is_none()); // Not yet spilled.
                    let r_y = self.outs[out_y].reg.expect("Spilled a non-register");
                    assert!(regs[r_y] == Some(out_y)); // Not yet overwritten.
                    spills[out_y] = Some(Slot(slots_used).into());
                    slots_used += 1;

                    Action::Push(Some(r_x.into()), Some(r_y.into()))
                },
                Node(n) => {
                    ins.extend(df.ins(n).iter().map(|&in_| {
                        // Read `in_` from a `Register` if possible.
                        match self.outs[in_].reg.filter(|&r| regs[r] == Some(in_)) {
                            Some(r) => Value::from(r),
                            None => spills[in_].expect("Value was overwritten but not spilled"),
                        }
                    }));
                    outs.extend(df.outs(n).map(|out| {
                        let r = self.outs[out].reg.expect("Wrote a non-register");
                        regs[r] = Some(out);
                        r
                    }));
                    Op::to_action(df.op(n), &outs, &ins)
                },
            });
        }
        // Work out which live values need to be moved where.
        let mut is_used = ArrayMap::new(NUM_REGISTERS);
        let mut dest_to_src: HashMap<Value, Value> =
            df.ins(exit_node).iter().zip(&self.after.live_values).map(|(&out, &dest)| {
                let src = match self.outs[out].reg.filter(|&r| regs[r] == Some(out)) {
                    // Read `in_` from a `Register` if possible.
                    Some(r) => Value::from(r),
                    None => spills[out].expect("Value was overwritten but not spilled")
                };
                if let Value::Register(r) = dest { is_used[r] = true; }
                if let Value::Register(r) = src { is_used[r] = true; }
                (dest, src)
            }).collect();
        // Create spill slots if necessary to match `after`.
        while slots_used < self.after.slots_used {
            let dest2 = Value::from(Slot(slots_used));
            let src2 = dest_to_src.remove(&dest2);
            slots_used += 1;
            let dest1 = Value::from(Slot(slots_used));
            let src1 = dest_to_src.remove(&dest1);
            slots_used += 1;
            ret.push(Action::Push(src1, src2));
        }
        // Move all live values into the expected `Value`s.
        // TODO: Find a way to schedule these `Move`s properly or to eliminate them.
        // We need a temporary `Register` that is not live.
        // If one is available, use it.
        // Otherwise, spill an arbitrary `Register` and use it.
        let spill_reg = REGISTERS[0]; // TODO: Pick more carefully.
        #[allow(clippy::option_if_let_else)]
        let (temp_value, temp_replacement) =
            if let Some(r) = all_registers().find(|&r| !is_used[r]) {
                // We found an unused `Register`.
                (r.into(), r.into())
            } else {
                // Spill `spill_reg` and use it.
                let spill_slot = Slot(slots_used);
                ret.push(Action::Push(None, Some(spill_reg.into())));
                slots_used += 2;
                (spill_reg.into(), spill_slot.into())
            };
        let is_temp_a_dest = dest_to_src.contains_key(&temp_value);
        ret.extend(moves(dest_to_src, &temp_value).map(|(mut dest, mut src)| {
            if src == temp_value { src = temp_replacement; }
            if dest == temp_value { dest = temp_replacement; }
            Action::Move(dest, src)
        }));
        if is_temp_a_dest {
            ret.push(Action::Pop(None, Some(spill_reg)));
            slots_used -= 2;
        }
        // Drop now-unused slots.
        assert!(self.after.slots_used <= slots_used);
        let num_drops = slots_used - self.after.slots_used;
        if num_drops > 0 {
            assert_eq!(num_drops & 1, 0);
            ret.push(Action::DropMany(num_drops >> 1));
        }
        // Return.
        ret.into()
    }
}

pub fn codegen(num_globals: usize, before: &Convention, after: &Convention, schedule: Schedule, exit_node: Node) -> Box<[Action]> {
    let mut codegen = CodeGen::new(num_globals, before, after, schedule);
    while let Some(node) = codegen.schedule.next() {
        codegen.add_node(node);
    }
    codegen.finish(exit_node)
}
