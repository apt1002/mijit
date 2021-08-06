use std::ops::{Index, IndexMut};

use crate::util::{AsUsize};
use super::{code};
use super::target::{Label, Word, Pool, Lower, Execute, Target};
use code::{Global};

// CaseId.
array_index! {
    /** Identifies a specialization of an `Engine`. */
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct CaseId(std::num::NonZeroUsize) {
        debug_name: "Specialization",
        UInt: usize,
    }
}

/**
 * Represents a basic block ending with some kind of branch.
 * See "doc/engine/structure.md".
 */
struct Case {
    fetch_label: Label,
}

//-----------------------------------------------------------------------------

/** An entry point into the compiled code. */
pub struct Entry {
    case: CaseId,
}

//-----------------------------------------------------------------------------

/**
 * This only exists to keep the borrow checker happy.
 * We might need to modify these fields while generating code.
 */
struct Internals {
    /**
     * The specializations in the order they were compiled, excluding the
     * least specialization. Indexed by [`Specialization`].
     */
    cases: Vec<Case>,
}

impl Internals {
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

//-----------------------------------------------------------------------------

/**
 * The state of the JIT compilation engine. This includes the memory allocated
 * for the compiled code, and all house-keeping data.
 */
#[allow(clippy::module_name_repetitions)]
pub struct Engine<T: Target> {
    /** The compilation target. */
    _target: T,
    /** The code compiled so far. */
    lowerer: T::Lowerer,
    /** This nested struct can be borrowed independently of `lowerer`. */
    internals: Internals,
}

impl<T: Target> Engine<T> {
    pub fn new(target: T, num_globals: usize) -> Self {
        let pool = Pool::new(num_globals);
        let lowerer = target.lowerer(pool);
        let internals = Internals {
            cases: Vec::new(),
        };
        Engine {_target: target, lowerer, internals}
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        &mut self.lowerer.pool_mut()[global]
    }

    /**
     * Call the compiled code starting at `entry`, passing the `Pool`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn execute(mut self, entry: Entry) -> std::io::Result<(Self, Word)> {
        let label = &self.internals[entry.case].fetch_label;
        let (lowerer, ret) = self.lowerer.execute(label, |f, pool| {
            let pool = pool.as_mut().as_mut_ptr();
            // Here is a good place to set a gdb breakpoint.
            f(pool, Word {u: 0})
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}
