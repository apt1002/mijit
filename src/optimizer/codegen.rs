use std::cmp::{max};

use super::{NUM_REGISTERS, ALLOCATABLE_REGISTERS, RegIndex, DUMMY_REG, Op, Schedule, RegisterPool, Placer};
use super::dataflow::{Dataflow, Out, DUMMY_OUT, Node};
use super::cost::{SPILL_COST, SLOT_COST};
use super::code::{Register, Slot, Value, Action};
use crate::util::{ArrayMap};

//-----------------------------------------------------------------------------

#[derive(Debug, Copy, Clone)]
enum Instruction {
    Absent,
    Spill(Out),
    Node(Node),
}

use Instruction::*;

impl Default for Instruction {
    fn default() -> Self {
        Absent
    }
}

//-----------------------------------------------------------------------------

/** The information that a [`CodeGen`] stores about each [`Out`]. */
#[derive(Debug)]
pub struct OutInfo {
    /** The time at which the `Out` became available, or [`usize::MAX`]. */
    time: usize,
    /** The register allocated for the `Out`, or [`DUMMY_REG`]. */
    reg: RegIndex,
}

impl Default for OutInfo {
    fn default() -> Self {
        OutInfo {
            time: usize::MAX,
            reg: DUMMY_REG,
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
    /** The [`Node`]s remaining to be processed. */
    schedule: Schedule<'a>,
    /** The [`Instruction`]s processed so far. */
    placer: Placer<Instruction>,
    /** An `OutInfo` for each `Out`. */
    outs: ArrayMap<Out, OutInfo>,
    /** The time at which each [`Node`] was executed. */
    node_times: ArrayMap<Node, usize>,
    /** The last time at which each [`Reg`] is used, or zero. */
    reg_times: ArrayMap<RegIndex, usize>,
    /** The register allocator state. */
    pool: RegisterPool<Out>,
}

impl<'a> CodeGen<'a> {
    pub fn new(schedule: Schedule<'a>) -> Self {
        let df: &'a Dataflow = schedule.dataflow;
        // Initialize the datastructures with the live registers of the
        // starting `Convention`.
        let placer = Placer::new();
        let cg = CodeGen {
            schedule: schedule,
            placer: placer,
            outs: df.out_map(),
            node_times: df.node_map(),
            reg_times: ArrayMap::new(super::NUM_REGISTERS),
            pool: RegisterPool::new(ArrayMap::new(super::NUM_REGISTERS)),
        };
        // TODO: Fill in various fields based on entry Convention.
        cg
    }

    /** `true` if we've placed an [`Instruction::Spill`] for `out`. */
    fn is_spilled(&self, out: Out) -> bool {
        *self.pool.reg_info(self.outs[out].reg) != Some(out)
    }

    /** Record that we used `ri` at `time` (either reading or writing). */
    fn use_reg(&mut self, ri: RegIndex, time: usize) {
        self.reg_times[ri] = max(self.reg_times[ri], time);
    }

    /** Called for each [`Node`] in the [`Schedule`] in forwards order. */
    pub fn add_node(&mut self, node: Node) {
        let df: &'a Dataflow = self.schedule.dataflow;
        let mut time = 0; // Earliest time (in cycles) when we can place `node`.
        // Free every input register that won't be used again.
        for &in_ in df.ins(node) {
            if self.schedule.first_use(in_).is_none() && !self.is_spilled(in_) {
                self.pool.free(self.outs[in_].reg);
            }
        }
        // Spill until we have enough registers to hold the outputs of `node`.
        let num_outs = df.num_outs(node);
        while self.pool.num_clean() < num_outs {
            let schedule = &self.schedule; // Appease borrow-checker.
            let (ri, out) = self.pool.spill(|&out| schedule.first_use(out));
            let mut time = self.outs[out].time;
            self.placer.add_item(Spill(out), SPILL_COST, &mut time);
            self.use_reg(ri, time);
        }
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
            self.outs[out].reg = ri;
            time = max(time, self.reg_times[ri]);
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if df.ins(node).iter().any(|&in_| self.is_spilled(in_)) {
            // We can't be sure it's not still in a register; this is a guess.
            resources += SLOT_COST;
        }
        self.placer.add_item(Node(node), resources, &mut time);
        // Record the node's placement.
        self.node_times[node] = time;
        // Record when the inputs were used.
        for &in_ in df.ins(node) {
            if !self.is_spilled(in_) {
                self.use_reg(self.outs[in_].reg, time);
            }
        }
        // Record when the outputs become available.
        for (out, &latency) in df.outs(node).zip(df.cost(node).output_latencies) {
            self.reg_times[self.outs[out].reg] = time;
            self.outs[out].time = time + latency as usize;
        }
    }

    /**
     * Allocate spill slots, resolve operands, convert all instructions to
     * [`Action`]s, and return them in the order they should be executed in.
     */
    pub fn finish(self, num_slots: &mut usize) -> Vec<Action> {
        let dataflow = self.schedule.dataflow;
        // Initialise bindings.
        let register_to_index = super::map_from_register_to_index();
        let mut spills: ArrayMap<Out, Option<Slot>> = dataflow.out_map();
        let mut regs: ArrayMap<RegIndex, Out> = ArrayMap::new_with(NUM_REGISTERS, || DUMMY_OUT);
        for (out, &value) in dataflow.outs(dataflow.entry_node()).zip(dataflow.inputs()) {
            match value {
                Value::Register(r) => {
                    let ri = *register_to_index.get(&r).expect("Not an allocatable register");
                    regs[ri] = out;
                },
                Value::Slot(s) => {
                    assert!(s.0 < *num_slots);
                    spills[out] = Some(s);
                },
            }
        }
        // Build the list of instructions.
        let mut ret: Vec<_> = self.placer.iter().map(|instruction| {
            match instruction {
                &Absent => panic!("Absent instruction"),
                &Spill(s) => {
                    assert!(spills[s].is_none()); // Not yet spilled.
                    let ri = self.outs[s].reg;
                    assert!(regs[ri] == s); // Not yet overwritten.
                    let slot = Slot(*num_slots);
                    *num_slots += 1;
                    spills[s] = Some(slot);
                    Action::Move(slot.into(), ALLOCATABLE_REGISTERS[ri.0].into())
                },
                &Node(n) => {
                    let outs: Vec<Register> = dataflow.outs(n)
                        .map(|dest| ALLOCATABLE_REGISTERS[self.outs[dest].reg.0])
                        .collect();
                    let ins: Vec<Value> = dataflow.ins(n).iter().map(|&src| {
                        let ri = self.outs[src].reg;
                        if regs[ri] == src {
                            ALLOCATABLE_REGISTERS[ri.0].into()
                        } else {
                            spills[src].expect("Value was overwritten but not spilled").into()
                        }
                    }).collect();
                    Op::to_action(dataflow.op(n), &outs, &ins)
                },
            }
        }).collect();
        // TODO: If the ending `Convention` has live registers, generate and
        // schedule move instructions.
        ret.shrink_to_fit();
        ret
    }
}

pub fn codegen(schedule: Schedule) -> Vec<Action>
{
    let mut codegen = CodeGen::new(schedule);
    while let Some(node) = codegen.schedule.next() {
        codegen.add_node(node);
    }
    let mut num_slots = 0;
    codegen.finish(&mut num_slots)
}
