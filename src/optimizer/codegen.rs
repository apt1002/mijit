use super::{Out, Node, Schedule};
use super::code::{Action, Slot, Register};
use crate::util::{ArrayMap, AsUsize};

/** Records the storage allocated for a particular [`Out`]. */
#[derive(Debug, Default)]
struct Binding {
    slot: Option<Slot>,
    register: Option<Register>,
}

/** An index into [`ALLOCATABLE_REGISTERS`]. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
struct RegIndex(usize);

impl AsUsize for RegIndex {
    fn as_usize(self) -> usize {
        self.0
    }
}

struct CodeGen<'a> {
    schedule: Schedule<'a>,
    _bindings: ArrayMap<Out, Binding>,
}

impl<'a> CodeGen<'a> {
    pub fn new(schedule: Schedule<'a>) -> Self {
        // Initialize the datastructures with the live registers of the
        // starting `Convention`.
        let bindings = schedule.dataflow.out_map();
        CodeGen {
            schedule: schedule,
            _bindings: bindings, //TODO
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

    pub fn finish(self) -> Vec<Action> {
        // If the ending `Convention` has live registers, generate and schedule
        // move instructions.

        // Serialize the cycles into a list of actions.
        let actions = Vec::new(); //...
        actions
    }
}

pub fn codegen(schedule: Schedule) -> Vec<Action>
{
    let mut codegen = CodeGen::new(schedule);
    while let Some(node) = codegen.schedule.next() {
        codegen.add_node(node);
    }
    codegen.finish()
}
