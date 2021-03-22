use std::cmp::{max};
use std::collections::{HashMap};
use std::fmt::{self, Debug, Formatter};

use super::{
    Convention,
    NUM_REGISTERS, ALLOCATABLE_REGISTERS, RegIndex, map_from_register_to_index, DUMMY_REG,
    Op, Schedule, RegisterPool, Placer, moves,
};
use super::dataflow::{Dataflow, Out, DUMMY_OUT, Node};
use super::cost::{SPILL_COST, SLOT_COST};
use super::code::{Register, Slot, Value, Action};
use crate::util::{ArrayMap};

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
    /** The register allocated for the `Out`, or [`DUMMY_REG`]. */
    ri: RegIndex,
}

impl Debug for OutInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "OutInfo {{time: {:?}, ri: {:?}}}", self.time, self.ri)
    }
}

impl Default for OutInfo {
    fn default() -> Self {
        OutInfo {
            time: usize::MAX,
            ri: DUMMY_REG,
        }
    }
}

/** The information that a [`CodeGen`] stores about each [`RegIndex`]. */
pub struct RegInfo {
    /** The last time at which each [`Reg`] is used, or zero. */
    time: usize,
    /** The contents of the register at the current time. */
    out: Out,
}

impl Debug for RegInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "RegInfo {{time: {:?}, out: {:?}}}", self.time, self.out)
    }
}

impl Default for RegInfo {
    fn default() -> Self {
        RegInfo {
            time: 0,
            out: DUMMY_OUT,
        }
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
    regs: ArrayMap<RegIndex, RegInfo>,
    /** The register allocator state. */
    pool: RegisterPool<Out>,
}

impl<'a> CodeGen<'a> {
    pub fn new(before: &'a Convention, after: &'a Convention, schedule: Schedule<'a>) -> Self {
        let df: &'a Dataflow = schedule.dataflow;
        // Initialize the data structures with the live registers of `before`.
        let reg_map = map_from_register_to_index();
        let mut dirty = ArrayMap::new(super::NUM_REGISTERS);
        let mut outs: ArrayMap<Out, OutInfo> = df.out_map();
        let mut regs: ArrayMap<RegIndex, RegInfo> = ArrayMap::new(super::NUM_REGISTERS);
        for (out, &value) in df.outs(df.entry_node()).zip(&before.live_values) {
            if !schedule.first_use(out).is_none() {
                match value {
                    Value::Register(r) => {
                        let &ri = reg_map.get(&r).expect("Not an allocatable register");
                        dirty[ri] = Some(out);
                        regs[ri].out = out;
                        outs[out].ri = ri;
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

    /** `true` if `out` is in a register. */
    fn is_reg(&self, out: Out) -> bool {
        let ri = self.outs[out].ri;
        ri != DUMMY_REG && self.regs[ri].out == out
    }

    /** Record that we used `ri` at `time` (either reading or writing). */
    fn use_reg(&mut self, ri: RegIndex, time: usize) {
        self.regs[ri].time = max(self.regs[ri].time, time);
    }

    /** Spills values until at least `num_required` registers are free. */
    fn spill_until(&mut self, num_required: usize) {
        while self.pool.num_clean() < num_required {
            let schedule = &self.schedule; // Appease borrow-checker.
            let (ri, out) = self.pool.spill(|&out| schedule.first_use(out));
            let mut time = self.outs[out].time;
            self.placer.add_item(Spill(out), SPILL_COST, &mut time);
            self.use_reg(ri, time);
        }
    }

    /** Called for each [`Node`] in the [`Schedule`] in forwards order. */
    pub fn add_node(&mut self, node: Node) {
        let df: &'a Dataflow = self.schedule.dataflow;
        let mut time = 0; // Earliest time (in cycles) when we can place `node`.
        // Free every input register that won't be used again.
        for &in_ in df.ins(node) {
            if self.schedule.first_use(in_).is_none() && self.is_reg(in_) {
                let d = self.pool.free(self.outs[in_].ri);
                assert_eq!(d, in_);
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
            let ri = self.pool.allocate(out);
            self.outs[out].ri = ri;
            time = max(time, self.regs[ri].time);
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if df.ins(node).iter().any(|&in_| !self.is_reg(in_)) {
            // We can't be sure it's not still in a register; this is a guess.
            resources += SLOT_COST;
        }
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times[node] = time;
        // Record when the inputs were used.
        for &in_ in df.ins(node) {
            if self.is_reg(in_) {
                self.use_reg(self.outs[in_].ri, time);
            }
        }
        // Record when the outputs become available.
        for (out, &latency) in df.outs(node).zip(df.cost(node).output_latencies) {
            self.regs[self.outs[out].ri] = RegInfo {time, out};
            self.outs[out].time = time + latency as usize;
        }
    }

    /**
     * Allocate spill slots, resolve operands, convert all instructions to
     * [`Action`]s, and return them in the order they should be executed in.
     */
    pub fn finish(self, exit_node: Node) -> Vec<Action> {
        let df: &'a Dataflow = self.schedule.dataflow;
        // Initialise bindings.
        let mut num_slots = self.before.slots_used;
        let register_to_index = super::map_from_register_to_index();
        let mut spills: ArrayMap<Out, Option<Slot>> = df.out_map();
        let mut regs: ArrayMap<RegIndex, Out> = ArrayMap::new_with(NUM_REGISTERS, || DUMMY_OUT);
        for (out, &value) in df.outs(df.entry_node()).zip(&self.before.live_values) {
            match value {
                Value::Register(r) => {
                    let ri = *register_to_index.get(&r).expect("Not an allocatable register");
                    regs[ri] = out;
                },
                Value::Slot(s) => {
                    assert!(s.0 < num_slots);
                    spills[out] = Some(s);
                },
            }
        }
        // Build the list of instructions.
        let mut ret: Vec<_> = self.placer.iter().map(|instruction| {
            match instruction {
                &Absent => panic!("Absent instruction"),
                &Spill(out) => {
                    assert!(spills[out].is_none()); // Not yet spilled.
                    let ri = self.outs[out].ri;
                    assert!(regs[ri] == out); // Not yet overwritten.
                    let slot = Slot(num_slots);
                    num_slots += 1;
                    spills[out] = Some(slot);
                    Action::Move(slot.into(), ALLOCATABLE_REGISTERS[ri.0].into())
                },
                &Node(n) => {
                    let ins: Vec<Value> = df.ins(n).iter().map(|&in_| {
                        let ri = self.outs[in_].ri;
                        let src = if ri != DUMMY_REG && regs[ri] == in_ {
                            ALLOCATABLE_REGISTERS[ri.0].into()
                        } else {
                            spills[in_].expect("Value was overwritten but not spilled").into()
                        };
                        src
                    }).collect();
                    let outs: Vec<Register> = df.outs(n).map(|out| {
                        let ri = self.outs[out].ri;
                        regs[ri] = out;
                        let dest = ALLOCATABLE_REGISTERS[ri.0];
                        dest
                    }).collect();
                    Op::to_action(df.op(n), &outs, &ins)
                },
            }
        }).collect();
        // Move all live values into the expected `Value`s.
        // TODO: Find a way to schedule these `Move`s properly or eliminate them.
        let dest_to_src: HashMap<Value, Value> =
            df.ins(exit_node).iter().zip(&self.after.live_values).map(|(&out, &dest)| {
                let ri = self.outs[out].ri;
                let src = if ri != DUMMY_REG && regs[ri] == out {
                    ALLOCATABLE_REGISTERS[ri.0].into()
                } else {
                    spills[out].expect("Value was overwritten but not spilled").into()
                };
                (dest, src)
            }).collect();
        let temp_reg: Value = ALLOCATABLE_REGISTERS.iter()
            .map(|&r| Value::from(r))
            .find(|&r| !dest_to_src.contains_key(&r))
            .unwrap_or_else(|| {
                let slot = Slot(num_slots);
                num_slots += 1;
                slot.into()
            });
        ret.extend(moves(dest_to_src, temp_reg).map(|(dest, src)| Action::Move(dest, src)));
        // Return.
        ret.shrink_to_fit();
        ret
    }
}

pub fn codegen(before: &Convention, after: &Convention, schedule: Schedule, exit_node: Node) -> Vec<Action> {
    let mut codegen = CodeGen::new(before, after, schedule);
    while let Some(node) = codegen.schedule.next() {
        codegen.add_node(node);
    }
    codegen.finish(exit_node)
}
