use std::ops::{Index, IndexMut};

use crate::util::{AsUsize};
use super::{code};
use super::target::{Label, Counter, Word, Pool, Lower, Execute, Target, RESULT};
use code::{Precision, Global, Switch, Action};
use Precision::*;

// CaseId.
array_index! {
    /** Identifies a [`Case`] of an [`Engine`]. */
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct CaseId(std::num::NonZeroUsize) {
        debug_name: "CaseId",
        UInt: usize,
    }
}

/** The part of a [`Case`] which changes when it is specialized. */
enum Junction {
    /** Not yet specialized. Count, and retire to another [`Case`]. */
    Retire {
        /** The profiling [`Counter`] to increment. */
        counter: Counter,
        /** The code to run. */
        retire_code: Box<[Action]>,
        /** The [`Case`] to jump to. `None` means the root. */
        jump: Option<CaseId>,
    },
    /** Specialized. Run special code and pick a continuation. */
    Fetch {
        /** The code to run. */
        fetch_code: Box<[Action]>,
        /** The control-flow decision. */
        switch: Switch<CaseId>,
    },
}

use Junction::*;

/**
 * Represents a basic block ending with some kind of branch.
 * See "doc/engine/structure.md".
 */
struct Case {
    label: Label,
    junction: Junction,
}

//-----------------------------------------------------------------------------

/** An entry point into the compiled code. */
pub struct Entry {
    label: Label,
    case: CaseId,
}

//-----------------------------------------------------------------------------

/**
 * This only exists to keep the borrow checker happy.
 * We might need to modify these fields while generating code.
 */
struct Internals {
    /**
     * The [`Case`]s in the order they were compiled, excluding the root.
     * Indexed by [`CaseId`].
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
    /** The number of [`Slot`]s at every [`Entry`]'s `Case`. */
    num_slots: usize,
    /** Executed on entry. */
    prologue: Box<[Action]>,
    /** Executed on exit. */
    epilogue: Box<[Action]>,
    /** The code compiled so far. */
    lowerer: T::Lowerer,
    /** This nested struct can be borrowed independently of `lowerer`. */
    internals: Internals,
}

impl<T: Target> Engine<T> {
    /**
     * Constructs an `Engine`, initially with no [`Entry`]s.
     *  - num_globals - the number of `Global`s needed to pass values to and
     *    from the compiled code.
     *  - num_slots - the number of `Slot`s that are live at every `Entry`.
     *    Must be even.
     *  - prologue - executed on every entry to the compiled code.
     *  - epilogue - executed on every exit from the compiled code.
     */
    pub fn new(target: T, num_globals: usize, num_slots: usize, prologue: Box<[Action]>, epilogue: Box<[Action]>) -> Self {
        assert_eq!(num_slots & 1, 0);
        let pool = Pool::new(num_globals);
        let lowerer = target.lowerer(pool);
        let internals = Internals {
            cases: Vec::new(),
        };
        Engine {_target: target, num_slots, prologue, epilogue, lowerer, internals}
    }

    /** Borrows the value of variable `global`. */
    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        &mut self.lowerer.pool_mut()[global]
    }

    /** Construct a fresh [`Case`] which retires to `jump`. */
    fn new_case(&mut self, retire_code: Box<[Action]>, jump: Option<CaseId>) -> CaseId {
        let lo = &mut self.lowerer;
        // Compile the mutable jump.
        let mut label = Label::new(None);
        lo.jump(&mut label);
        lo.define(&mut label);
        // Create a `Counter` and compile the code to increment it.
        let counter = lo.pool_mut().new_counter();
        lo.count(counter);
        // Compile `retire_code`.
        for &action in retire_code.iter() {
            lo.action(action);
        }
        // Compile the jump to `jump`.
        if let Some(jump) = jump {
            // Jump to a non-root `Case`.
            lo.jump(&mut self.internals[jump].label);
        } else {
            // Jump to the root.
            lo.epilogue()
        }
        // Record details in a `Case` and return its `CaseId`.
        let id = CaseId::new(self.internals.cases.len()).unwrap();
        self.internals.cases.push(Case {
            label,
            junction: Retire {counter, retire_code, jump}
        });
        id
    }

    /**
     * Construct an [`Entry`] to this `Engine`. Initially, the code at the
     * `Entry` will immediately return `exit_value`. To change this behaviour,
     * use `define()`.
     */
    pub fn new_entry(&mut self, exit_value: i64) -> Entry {
        assert!(exit_value >= 0);
        let lo = &mut self.lowerer;
        // Compile the prologue.
        let label = lo.here();
        lo.prologue();
        for _ in 0..(self.num_slots >> 1) {
            lo.action(Action::Push(None, None));
        }
        for &action in self.prologue.iter() {
            lo.action(action);
        }
        // Compile the epilogue.
        let mut retire_code = Vec::new();
        retire_code.extend(self.epilogue.iter().cloned());
        retire_code.push(Action::DropMany(self.num_slots >> 1));
        retire_code.push(Action::Constant(P64, RESULT, exit_value));
        let case = self.new_case(retire_code.into(), None);
        // Return.
        Entry {label, case}
    }

    /** Tests whether [`define(entry, ...)`] has been called. */
    pub fn is_defined(&self, entry: Entry) -> bool {
        matches!(self.internals[entry.case].junction, Fetch {..})
    }

    /**
     * Replace the code at `Entry` such that it executes `actions` and then
     * jumps to the `Entry` selected by `switch`. Each `Entry` may only be
     * defined once.
     */
    pub fn define(&mut self, entry: Entry, actions: Box<[Action]>, switch: Switch<Entry>) {
        assert!(!self.is_defined(entry));
    }

    /**
     * Call the compiled code starting at `entry`, passing the `Pool`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn run(mut self, entry: Entry) -> std::io::Result<(Self, Word)> {
        let (lowerer, ret) = self.lowerer.execute(&entry.label, |f, pool| {
            let pool = pool.as_mut().as_mut_ptr();
            // Here is a good place to set a gdb breakpoint.
            f(pool)
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}
