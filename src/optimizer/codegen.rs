use super::{Dataflow, Out, Node, Usage};
use super::code::{Action, Slot, Register, Value};
use super::lowerer::{ALLOCATABLE_REGISTERS};
use crate::util::{ArrayMap, AsUsize};

/** Records the storage allocated for a particular [`Out`]. */
#[derive(Debug, Default)]
struct Binding {
    slot: Option<Slot>,
    register: Option<Register>,
}

struct Cycle { }

/** An index into [`ALLOCATABLE_REGISTERS`]. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
struct RegIndex(usize);

impl AsUsize for RegIndex {
    fn as_usize(self) -> usize {
        self.0
    }
}

/** The status of a [`RegIndex`]. */
#[derive(Debug, Copy, Clone)]
enum RegState {
    /// The cycle in which the [`RegIndex`] became dead.
    Dead(usize),
    /// The contents of the [`RegIndex`].
    Alive(Out),
}

use RegState::*;

/**
 * Return the index in `it` of the element for which `f` gives the largest
 * non-None result.
 */
fn map_filter_max<I: IntoIterator, T: Ord> (
    it: I,
    mut f: impl FnMut(I::Item) -> Option<T>,
) -> Option<usize> {
    let mut it = it.into_iter().enumerate();
    while let Some((i, x)) = it.next() {
        if let Some(fx) = f(x) {
            let mut best = (i, fx);
            while let Some((j, y)) = it.next() {
                if let Some(fy) = f(y) {
                    if fy > best.1 {
                        best = (j, fy);
                    }
                }
            }
            return Some(best.0);
        }
    }
    None
}

struct CodeGen<'a> {
    dataflow: &'a Dataflow,
    usage: Usage<'a>,
    cycles: Vec<Cycle>,
    bindings: ArrayMap<Out, Binding>,
    regs: ArrayMap<RegIndex, RegState>,
}

impl<'a> CodeGen<'a> {
    pub fn new(dataflow: &'a Dataflow, usage: Usage<'a>) -> Self {
        // Initialize the datastructures with the live registers of the
        // starting `Convention`.
        CodeGen {
            dataflow: dataflow,
            usage: usage,
            cycles: Vec::new(),
            bindings: dataflow.out_map(), //TODO
            regs: ArrayMap::new_with(ALLOCATABLE_REGISTERS.len(), || Dead(0)), //TODO
        }
    }

    /**
     * Allocate a destination register for `out`.
     * If spilling is needed, find a cycle for the spill instruction.
     */
    fn allocate_destination_register(&mut self, out: Out, cycle: &mut usize) -> RegIndex {
        if let Some(r) = map_filter_max(&self.regs, |reg_state| {
            match reg_state{
                Dead(t) => Some(t), //FIXME
                Alive(out) => None,
            }
        }) {
            // We found one.
            panic!("TODO");
        }
        // Spill.
        panic!("TODO");
    }

    // Called for each node in the schedule in forwards order.
    pub fn add_node(&mut self, node: Node) {
        // Allocate destination registers for the outputs of `node`.
        let outs: Vec<_> = self.dataflow.outs(node).collect();
        let mut cycle: usize = 0;
        let out_regs: Vec<_> = outs.into_iter().map(
            |out| self.allocate_destination_register(out, &mut cycle)
        ).collect();
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

pub fn codegen(dataflow: &Dataflow, schedule: &[Node]) -> Vec<Action>
{
    // Build a list of the uses of each `Out`.
    let mut usage = Usage::new(dataflow);
    for &node in schedule.iter().rev() {
        for &in_ in dataflow.ins(node).iter().rev() {
            usage.push(in_);
        }
    }
    let mut codegen = CodeGen::new(dataflow, usage);
    for &node in schedule {
        codegen.add_node(node);
    }
    codegen.finish()
}
