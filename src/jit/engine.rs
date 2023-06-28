use std::collections::{HashMap};
use std::fmt::{Debug};
use std::ops::{Index, IndexMut};

use super::code::{Precision, Variable, Switch, Action, Marshal, EBB, Ending};
use Precision::*;
use super::graph::{Dataflow, Node, CFT, Convention, Propagator};
use super::target::{Label, Word, Lower, Execute, Target, RESULT};
use super::optimizer::{LookupLeaf, cft_to_ebb};
use crate::util::{AsUsize, push_and_return_index};

// CaseId.
array_index! {
    /// Identifies a [`Case`] of an [`Engine`].
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct CaseId(std::num::NonZeroUsize) {
        debug_name: "CaseId",
        UInt: usize,
    }
}

/// Represents a basic block ending with some kind of branch.
/// See `doc/engine/structure.md`.
///
/// One or both of `fetch` and `retire` must be non-`None` for every reachable
/// `Case`, as must `convention` (they can all be `None` during construction).
#[derive(Debug)]
struct Case {
    /// The unique [`Switch`] that can jump directly to this `Case`.
    fetch_parent: Option<CaseId>,
    /// The [`Convention`] on entry (i.e. at `label`).
    before: Option<Convention>,

}

impl Case {
    pub fn convention(&self) -> &Convention {
        assert!(self.retire.is_some() || self.fetch.is_some());
        self.before.as_ref().expect("Incompletely constructed")
    }

    /// If `self.before` is `None`, replaces it with `new`.
    /// Otherwise, assert that `new` refines `self.before`.
    fn set_convention(&mut self, new: Convention) {
        if let Some(old) = &self.before {
            assert!(new.refines(old));
        } else {
            self.before = Some(new);
        }
    }
}

//-----------------------------------------------------------------------------

/// This only exists to keep the borrow checker happy.
/// We might need to borrow these fields while generating code.
#[derive(Debug)]
struct Internals {
    /// The [`Convention`] obeyed by the root.
    convention: Convention,
    /// The [`Case`]s in the order they were compiled, excluding the root.
    /// Indexed by [`CaseId`].
    cases: Vec<Case>,
}

impl Internals {
    /// Find the [`Convention`] for a [`CaseId`] allowing for `None`.
    fn convention(&self, id: impl Into<Option<CaseId>>) -> &Convention {
        id.into().map_or(&self.convention, |id| self[id].convention())
    }
}

impl Index<CaseId> for Internals {
    type Output = Case;

    fn index(&self, id: CaseId) -> &Self::Output {
        &self.cases[id.as_usize()]
    }
}

impl IndexMut<CaseId> for Internals {
    fn index_mut(&mut self, id: CaseId) -> &mut Self::Output {
        &mut self.cases[id.as_usize()]
    }
}

impl<'a> LookupLeaf for Internals {
    type Leaf = CaseId;

    /// Return the convention in effect at `leaf`.
    fn convention(&self, leaf: &CaseId) -> &Convention {
        self.convention(*leaf)
    }

    /// Return the estimated relative frequency of `leaf`.
    fn weight(&self, _leaf: &CaseId) -> usize {
        1  // FIXME
    }
}

//-----------------------------------------------------------------------------

/// The state of the JIT compilation engine. This includes the memory allocated
/// for the compiled code, and all house-keeping data.
#[allow(clippy::module_name_repetitions)]
pub struct Engine<T: Target> {
    /// The compilation target.
    _target: T,
    /// The code compiled so far.
    lowerer: T::Lowerer,
    /// The ambient [`Dataflow`] graph that accumulates compiled code.
    dataflow: Dataflow,
    /// This nested struct can be borrowed independently of `lowerer`.
    i: Internals,
}

impl<T: Target> std::fmt::Debug for Engine<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("Engine")
            .field("cases", &self.i.cases)
            .finish()
    }
}

impl<T: Target> Engine<T> {
    /// Constructs an `Engine`, initially with no entries.
    pub fn new(target: T) -> Self {
        let lowerer = target.lowerer();
        let dataflow = Dataflow::new();
        let i = Internals {
            convention: Convention::default(),
            cases: Vec::new(),
        };
        Engine {_target: target, lowerer, dataflow, i}
    }

    /// Simultaneously borrow the [`Dataflow`] and a [`LookupLeaf`].
    pub fn dataflow_mut(&mut self) -> (&mut Dataflow, &impl LookupLeaf<Leaf=CaseId>) {
        (&mut self.dataflow, &self.i)
    }

    fn new_exit(&mut self, reason: u32) -> CaseId {
        // TODO.
    }

    fn new_label(
        &mut self,
        lives: &[Register],
        epilogue: impl FnOnce(Builder<CaseId>, &[Node]) -> CFT<CaseId>,
    ) -> CaseId {
        // TODO.
    }

    fn new_entry(
        &mut self,
        prologue: impl FnOnce(Builder<CaseId>, Node) -> CFT<CaseId>,
    ) -> Label {
        // TODO.
    }

    /// Define the code for case `id`.
    ///
    /// - id - the case to modify.
    /// - slots_used - the number of [`Slot`]s that exist on entry to `cft`.
    /// - input_map - the [`Variable`] allocation on entry to `cft`.
    /// - cft - the control-flow tree defining the desired behaviour.
    pub fn define(
        &mut self,
        id: CaseId,
        slots_used: usize, // TODO: Remove.
        input_map: &HashMap<Node, Variable>, // TODO: Remove.
        cft: &CFT<CaseId>,
    ) {
        let ebb = cft_to_ebb(
            &self.dataflow,
            slots_used,
            input_map,
            cft,
            &self.i,
        );
        self.build_inner(id, ebb)
    }

    /// Call the compiled code starting at `label`.
    /// - global - the value to pass in [`GLOBAL`].
    ///
    /// # Safety
    ///
    /// This will crash if the code is compiled for the wrong [`Target`] or if
    /// the code is invalid.
    pub unsafe fn run(&mut self, label: &Label, global: *mut ()) -> Word {
        self.lowerer.execute(label, |f| {
            // Here is a good place to set a debugger breakpoint.
            f(global)
        })
    }
}
