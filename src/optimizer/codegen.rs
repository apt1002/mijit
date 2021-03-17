use super::{NUM_REGISTERS, ALLOCATABLE_REGISTERS, Op, Out, DUMMY_OUT, Node, Schedule, RegisterPool, RegIndex, Placer};
use super::code::{Register, Slot, Value, Action};
use crate::util::{ArrayMap};

enum Instruction {
    Absent,
    _Spill(Out),
    _Node(Node),
}

use Instruction::*;

impl Default for Instruction {
    fn default() -> Self {
        Absent
    }
}

/** The state of the code generation algorithm. */
struct CodeGen<'a> {
    /** The [`Node`]s remaining to be processed. */
    schedule: Schedule<'a>,
    /** The register allocator state. */
    _pool: RegisterPool<usize, Out>,
    /** The register allocation decisions. */
    dest_regs: ArrayMap<Out, RegIndex>,
    /** The [`Instruction`]s processed so far. */
    placer: Placer<Instruction>,
}

impl<'a> CodeGen<'a> {
    pub fn new(schedule: Schedule<'a>) -> Self {
        // Initialize the datastructures with the live registers of the
        // starting `Convention`.
        let pool = RegisterPool::new(ArrayMap::new(super::NUM_REGISTERS), |_| 0);
        let dest_regs = schedule.dataflow.out_map();
        let placer = Placer::new();
        CodeGen {
            schedule: schedule,
            _pool: pool, // TODO.
            dest_regs: dest_regs, // TODO.
            placer: placer,
        }
    }

    // Called for each node in the schedule in forwards order.
    pub fn add_node(&mut self, _node: Node) {
        // Allocate destination registers for the outputs of `node`.

        // Find the first cycle after the dependencies and operands of the
        // node and the destination registers become available.

        // Advance until we find a cycle where the execution resources are
        // available.

        // Insert the node into that cycle and decrement the budget.
        // Update all the datastructures about register usage etc.
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
                &_Spill(s) => {
                    assert!(spills[s].is_none()); // Not yet spilled.
                    let ri = self.dest_regs[s];
                    assert!(regs[ri] == s); // Not yet overwritten.
                    let slot = Slot(*num_slots);
                    *num_slots += 1;
                    spills[s] = Some(slot);
                    Action::Move(slot.into(), ALLOCATABLE_REGISTERS[ri.0].into())
                },
                &_Node(n) => {
                    let outs: Vec<Register> = dataflow.outs(n)
                        .map(|dest| ALLOCATABLE_REGISTERS[self.dest_regs[dest].0])
                        .collect();
                    let ins: Vec<Value> = dataflow.ins(n).iter().map(|&src| {
                        let ri = self.dest_regs[src];
                        if regs[ri] == src {
                            ALLOCATABLE_REGISTERS[ri.0].into()
                        } else {
                            spills[src].expect("Value was overwritten but not spilled").into()
                        }
                    }).collect();
                    Op::to_action(dataflow.node(n), &outs, &ins).unwrap()
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
