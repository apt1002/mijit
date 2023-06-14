use super::{code, graph, Engine, CaseId};
use code::{Register, EBB};
use graph::{Op, Node, CFT, Builder};
use super::target::{Label, Word, Target};
use super::optimizer::{simulate, LookupLeaf};
use crate::util::{AsUsize, reverse_map, push_and_return_index};

// EntryId.
array_index! {
    /// Identifies an entry point of an [`Jit`].
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct EntryId(std::num::NonZeroUsize) {
        debug_name: "EntryId",
        UInt: usize,
    }
}

/// An entry point into the compiled code.
#[derive(Debug)]
struct Entry {
    label: Label,
    case: CaseId,
    is_defined: bool,
}

//-----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Jit<T: Target> {
    engine: Engine<T>,
    /// Indexed by `EntryId`.
    entries: Vec<Entry>,
}

// Use a macro, not a method, to keep the borrow-checker happy.
macro_rules! get {
    ($self: expr, $id: expr) => ($self.entries[$id.as_usize()])
}

impl<T: Target> Jit<T> {
    pub fn new(target: T) -> Self {
        Self {
            engine: Engine::new(target),
            entries: Vec::new(),
        }
    }

    /// Constructs a new entry/exit point. This is also a point where an
    /// interrupt can occur.
    ///
    /// Initially, the code at the entry point will immediately exit, returning
    /// `exit_value`. Use `define()` to change its behaviour. The code passed to
    /// `define()` will be used when an interrupt has not occurred.
    ///
    /// - lives - the `Variable`s that are live at this point. A register
    ///   allocation hint.
    /// - prologue - code to restore state when resuming from an interrupt.
    /// - epilogue - code to save state before an interrupt.
    /// - exit_value - `run()` will return this value to its caller if
    ///   execution ends at this entry/exit point. Must be non-negative.
    pub fn new_entry<const N: usize>(
        &mut self,
        lives: &[Register; N], // TODO: Allow any `Variable`.
        prologue: impl FnOnce(Builder<()>, Node) -> CFT<()>,
        epilogue: impl FnOnce(Builder<()>, &[Node; N]) -> CFT<()>,
        exit_value: i64
    ) -> EntryId {
        let (label, case) = self.engine.new_entry(lives, prologue, epilogue, exit_value);
        EntryId::new(
            push_and_return_index(&mut self.entries, Entry {label, case, is_defined: false})
        ).unwrap()
    }

    /// Replace the code at `entry`. Each `EntryId` may only be defined once.
    ///
    ///  - entry - the entry point to modify.
    ///  - ebb - the extended basic block defining the desired behaviour.
    pub fn define(&mut self, entry: EntryId, ebb: EBB<EntryId>) {
        assert!(!get!(self, entry).is_defined);
        // Temporary: generate the `CFT` from the `EBB`.
        let ebb = ebb.map_once(&mut |id| get!(self, id).case);
        let (dataflow, lookup_leaf) = self.engine.dataflow_mut();
        let before = lookup_leaf.convention(&get!(self, entry).case);
        let slots_used = before.slots_used;
        let input_map = before.lives.iter()
            .map(|&variable| (dataflow.add_node(Op::Input, &[]), variable))
            .collect();
        let cft = simulate(
            dataflow,
            slots_used,
            reverse_map(&input_map),
            &ebb,
            lookup_leaf,
        );
        // Build it.
        self.engine.build(get!(self, entry).case, slots_used, &input_map, &cft);
        get!(self, entry).is_defined = true;
    }

    /// Call the compiled code starting at `entry`.
    /// - global - the value to pass in [`GLOBAL`].
    ///
    /// # Safety
    ///
    /// This will crash if the code is compiled for the wrong [`Target`] or if
    /// the code is invalid.
    pub unsafe fn run<G>(&mut self, entry: EntryId, global: &mut G) -> Word {
        let label = &get!(self, entry).label;
        self.engine.run(label, global as *mut G as *mut ())
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::super::target::{native};

    use super::super::factorial::*;

    #[test]
    pub fn factorial() {
        let mut jit = Factorial::new(native());
        let result = jit.run(5);
        assert_eq!(result, 120);
    }
}
