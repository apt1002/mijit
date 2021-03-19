use std::cmp::{max};

use super::{NUM_REGISTERS, ALLOCATABLE_REGISTERS, RegIndex, Op, Schedule, RegisterPool, Placer};
use super::dataflow::{Dataflow, Out, DUMMY_OUT, Node};
use super::cost::{SPILL_COST, SLOT_COST};
use super::code::{Register, Slot, Value, Action};
use crate::util::{ArrayMap};

//-----------------------------------------------------------------------------

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

/** The state of the code generation algorithm. */
struct CodeGen<'a> {
    /** The [`Node`]s remaining to be processed. */
    schedule: Schedule<'a>,
    /** The [`Instruction`]s processed so far. */
    placer: Placer<Instruction>,
    /** The time at which each [`Out`] became available. */
    out_times: ArrayMap<Out, usize>,
    /** The time at which each [`Node`] was executed. */
    node_times: ArrayMap<Node, usize>,
    /** The time at which each [`Reg`] becomes clean, or `usize::MAX`. */
    reg_times: ArrayMap<RegIndex, usize>,
    /** The register allocator state. */
    pool: RegisterPool<Out>,
    /** The register allocation decisions. */
    out_regs: ArrayMap<Out, RegIndex>,
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
            out_times: df.out_map(),
            node_times: df.node_map(),
            reg_times: ArrayMap::new_with(super::NUM_REGISTERS, || usize::MAX),
            pool: RegisterPool::new(ArrayMap::new(super::NUM_REGISTERS)),
            out_regs: df.out_map(), // Initially all `DUMMY_REG`.
        };
        // TODO: Fill in various fields based on entry Convention.
        cg
    }

    /** Tests whether we've placed a `Spill` for `out`. */
    pub fn is_spilled(&self, out: Out) -> bool {
        self.reg_times[self.out_regs[out]] != usize::MAX
    }

    /** Called for each [`Node`] in the schedule in forwards order. */
    pub fn add_node(&mut self, node: Node) {
        let df: &'a Dataflow = self.schedule.dataflow;
        let mut time = 0; // Earliest time (in cycles) when we can place `node`.
        // Spill until we have enough registers to hold the outputs of `node`.
        let num_outs = df.num_outs(node);
        while self.pool.num_clean() < num_outs {
            let schedule = &self.schedule; // Appease borrow-checker.
            let (ri, out) = self.pool.spill(|&out| schedule.first_use(out));
            self.reg_times[ri] = self.out_times[out];
            self.placer.add_item(Spill(out), SPILL_COST, &mut self.reg_times[ri]);
        }
        // Bump `time` until the dependencies are available.
        for &dep in df.deps(node) {
            time = max(time, self.node_times[dep]);
        }
        // Bump `time` until the operands are available.
        for (&in_, &latency) in df.ins(node).iter().zip(df.cost(node).input_latencies) {
            time = max(time, self.out_times[in_] + latency as usize);
        }
        // Bump `time` until some destination registers are available.
        for out in df.outs(node) {
            let ri = self.pool.allocate(out);
            self.out_regs[out] = ri;
            self.reg_times[ri] = usize::MAX;
            time = max(time, self.reg_times[ri]);
        }
        // Bump `time` until the execution resources are available.
        let mut resources = df.cost(node).resources;
        if df.ins(node).iter().any(|&in_| self.is_spilled(in_)) {
            // We can't be sure it's not still in a register; this is a guess.
            resources += SLOT_COST;
        }
        self.placer.add_item(Node(node), resources, &mut time);
        // Record when the outputs become available.
        self.node_times[node] = time;
        for (out, &latency) in df.outs(node).zip(df.cost(node).output_latencies) {
            self.out_times[out] = time + latency as usize;
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
                    let ri = self.out_regs[s];
                    assert!(regs[ri] == s); // Not yet overwritten.
                    let slot = Slot(*num_slots);
                    *num_slots += 1;
                    spills[s] = Some(slot);
                    Action::Move(slot.into(), ALLOCATABLE_REGISTERS[ri.0].into())
                },
                &Node(n) => {
                    let outs: Vec<Register> = dataflow.outs(n)
                        .map(|dest| ALLOCATABLE_REGISTERS[self.out_regs[dest].0])
                        .collect();
                    let ins: Vec<Value> = dataflow.ins(n).iter().map(|&src| {
                        let ri = self.out_regs[src];
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
