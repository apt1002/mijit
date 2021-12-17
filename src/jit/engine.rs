use std::ops::{Index, IndexMut};

use crate::util::{AsUsize, AndOr};
use super::{code};
use super::target::{Label, Word, Pool, Lower, Execute, Target, RESULT};
use code::{Precision, Global, Switch, Action, Convention, Marshal};
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

/** A branch that merges with a [`Case`] that is less specialized. */
#[derive(Debug)]
struct Retire {
    /** The code to run. */
    actions: Box<[Action]>,
    /** The [`Case`] to jump to. `None` means the root. */
    jump: Option<CaseId>,
}

/** A branch to [`Case`]s that are more specialized. */
#[derive(Debug)]
struct Fetch {
    /** The code to run. */
    actions: Box<[Action]>,
    /** The control-flow decision. */
    switch: Switch<CaseId>,
}

/**
 * Represents a basic block ending with some kind of branch.
 * See `doc/engine/structure.md`.
 */
#[derive(Debug)]
struct Case {
    /** The unique [`Switch`] that can jump directly to this `Case`. */
    _fetch_parent: Option<CaseId>,
    /** The [`Convention`] on entry (i.e. at `label`). */
    convention: Convention,
    /** The address of the code. */
    label: Label,
    /** The part which changes when it is specialized. */
    junction: AndOr<Retire, Fetch>,
}

//-----------------------------------------------------------------------------

// EntryId.
array_index! {
    /** Identifies an entry point of an [`Engine`]. */
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct EntryId(std::num::NonZeroUsize) {
        debug_name: "EntryId",
        UInt: usize,
    }
}

/** An entry point into the compiled code. */
#[derive(Debug)]
pub struct Entry {
    label: Label,
    case: CaseId,
}

//-----------------------------------------------------------------------------

/**
 * This only exists to keep the borrow checker happy.
 * We might need to borrow these fields while generating code.
 */
struct Internals {
    /** The [`Convention`] obeyed by the root. */
    convention: Convention,
    /**
     * The [`Case`]s in the order they were compiled, excluding the root.
     * Indexed by [`CaseId`].
     */
    cases: Vec<Case>,
    /** Indexed by `EntryId`. */
    entries: Vec<Entry>,
}

impl Internals {
    fn new_entry(&mut self, label: Label, case: CaseId) -> EntryId {
        let index = self.entries.len();
        self.entries.push(Entry {label, case});
        EntryId::new(index).unwrap()
    }

    /** Find the [`Convention`] for a [`CaseId`] allowing for `None`. */
    fn convention(&self, id: impl Into<Option<CaseId>>) -> &Convention {
        id.into().map_or(&self.convention, |id| &self[id].convention)
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

impl Index<EntryId> for Internals {
    type Output = Entry;

    fn index(&self, entry: EntryId) -> &Self::Output {
        &self.entries[entry.as_usize()]
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
    i: Internals,
}

impl<T: Target> Engine<T> {
    /**
     * Constructs an `Engine`, initially with no entries.
     *  - num_globals - the number of [`Global`]s needed to pass values to and
     *    from the compiled code.
     */
    pub fn new(target: T, num_globals: usize) -> Self {
        let pool = Pool::new(num_globals);
        let lowerer = target.lowerer(pool);
        let i = Internals {
            convention: code::empty_convention(num_globals),
            cases: Vec::new(),
            entries: Vec::new(),
        };
        Engine {_target: target, lowerer, i}
    }

    /** Borrows the value of variable `global`. */
    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        &mut self.lowerer.pool_mut()[global]
    }

    /** Construct a fresh [`Case`] which retires to `jump`. */
    fn new_retire(&mut self, _fetch_parent: Option<CaseId>, convention: Convention, retire: Retire) -> CaseId {
        let lo = &mut self.lowerer;
        *lo.slots_used_mut() = convention.slots_used;
        // Compile the mutable jump.
        let mut label = Label::new(None);
        lo.jump(&mut label);
        lo.define(&mut label);
        // Compile `retire`.
        lo.actions(&*retire.actions);
        assert_eq!(*lo.slots_used_mut(), self.i.convention(retire.jump).slots_used);
        if let Some(jump) = retire.jump {
            // Jump to a non-root `Case`.
            lo.jump(&mut self.i[jump].label);
        } else {
            // Jump to the root.
            lo.epilogue()
        }
        // Record details in a `Case` and return its `CaseId`.
        let id = CaseId::new(self.i.cases.len()).unwrap();
        self.i.cases.push(Case {
            _fetch_parent,
            convention,
            label,
            junction: AndOr::A(retire),
        });
        id
    }

    /** Add a [`Fetch`] to a [`Case`] that only has a [`Retire`]. */
    fn add_fetch(&mut self, id: CaseId, fetch: Fetch) {
        let case = &mut self.i[id];
        let lo = &mut self.lowerer;
        *lo.slots_used_mut() = case.convention.slots_used;
        // Intercept all jumps to `id`.
        let mut here = lo.here();
        lo.steal(&mut case.label, &mut here);
        case.label = here;
        // Compile `fetch`.
        lo.actions(&*fetch.actions);
        match fetch.switch {
            Switch::Index {discriminant, ref cases, ref default_} => {
                for (index, &case) in cases.iter().enumerate() {
                    assert_eq!(*lo.slots_used_mut(), self.i.convention(case).slots_used);
                    lo.if_eq((discriminant, index as u64), &mut self.i[case].label);
                }
                assert_eq!(*lo.slots_used_mut(), self.i.convention(**default_).slots_used);
                lo.jump(&mut self.i[**default_].label);
            },
            Switch::Always(ref jump) => {
                assert_eq!(*lo.slots_used_mut(), self.i.convention(**jump).slots_used);
                lo.jump(&mut self.i[**jump].label);
            },
        }
        // Add `fetch` to `case` preserving its `retire`.
        let case = &mut self.i[id];
        let mut retire = Retire {actions: Box::new([]), jump: None}; // Dummy value.
        std::mem::swap(&mut retire, case.junction.b_mut().expect_err("Already specialized"));
        case.junction = AndOr::AB(retire, fetch);
    }

    /**
     * Construct an entry to this [`Engine`]. Initially, the code at the
     * entry will immediately return `exit_value`. To change this behaviour,
     * use [`define()`].
     *
     *  - prologue - executed on every entry to the compiled code.
     *  - convention - the [`Convention`] used after `prologue` and before
     *    `epilogue`.
     *  - epilogue - executed on every exit from the compiled code.
     *  - exit_value - returned to the caller on exit. Must be non-negative.
     */
    pub fn new_entry(&mut self, marshal: &Marshal, exit_value: i64) -> EntryId {
        assert_eq!(marshal.convention.slots_used & 1, 0);
        assert!(exit_value >= 0);
        let lo = &mut self.lowerer;
        *lo.slots_used_mut() = 0;
        // Compile the prologue.
        let label = lo.here();
        lo.prologue();
        lo.actions(&marshal.prologue);
        assert_eq!(*lo.slots_used_mut(), marshal.convention.slots_used);
        // Compile the epilogue.
        let mut actions = Vec::new();
        actions.extend(marshal.epilogue.iter().copied());
        actions.push(Action::Constant(P64, RESULT, exit_value));
        let retire = Retire {actions: actions.into(), jump: None};
        let case = self.new_retire(None, marshal.convention.clone(), retire);
        // Return.
        self.i.new_entry(label, case)
    }

    /** Tests whether [`define(entry, ...)`] has been called. */
    pub fn is_defined(&self, entry: EntryId) -> bool {
        match self.i[self.i[entry].case].junction {
            AndOr::A(ref _retire) => false,
            AndOr::B(ref _fetch) => panic!("Impossible"),
            AndOr::AB(ref _retire, ref _fetch) => true,
        }
    }

    /**
     * Replace the code at `entry` such that it executes `actions` and then
     * jumps to the [`EntryId`] selected by `switch`. Each `EntryId` may only
     * be defined once.
     */
    pub fn define(&mut self, entry: EntryId, actions: Box<[Action]>, switch: &Switch<EntryId>) {
        assert!(!self.is_defined(entry));
        let switch = switch.map(|&e: &EntryId| {
            let case_id = self.i[e].case;
            self.new_retire(
                Some(self.i[entry].case),
                self.i[case_id].convention.clone(),
                Retire {actions: Box::new([]), jump: Some(case_id)},
            )
        });
        self.add_fetch(self.i[entry].case, Fetch {actions, switch});
    }

    /**
     * Returns a copy of the hot path starting at `id` up to the next
     * [`Switch`]. Returns `None` if the hot path exits Mijit without reaching
     * a `Switch`.
     */
    fn hot_path(&self, mut id: CaseId) -> Option<(Vec<Action>, Switch<CaseId>)> {
        let mut actions = Vec::new();
        loop {
            match self.i[id].junction.b() {
                Ok(fetch) => {
                    // Succeed.
                    actions.extend(fetch.actions.iter().copied());
                    return Some((actions, fetch.switch.clone()));
                },
                Err(retire) => {
                    actions.extend(retire.actions.iter().copied());
                    if let Some(jump) = retire.jump {
                        // Loop.
                        id = jump;
                    } else {
                        // Fail.
                        return None;
                    }
                },
            }
        }
    }

    /**
     * Find the hot path starting at `id`, which must be a [`Retire`].
     * Clone it, optimize it, and replace `id` with a [`Fetch`].
     */
    // TODO: Make private. Revealing it suppresses several "unused" warnings.
    pub fn specialize(&mut self, id: CaseId) {
        assert!(self.i[id].junction.b().is_err());
        if let Some((actions, switch)) = self.hot_path(id) {
            // TODO: Optimize.
            let fetch = Fetch {
                actions: actions.into(),
                switch: switch.map(|&jump| self.new_retire(
                    Some(id),
                    self.i.convention(jump).clone(),
                    Retire {actions: Box::new([]), jump: Some(jump)},
                )),
            };
            self.add_fetch(id, fetch);
        }
    }

    /**
     * Call the compiled code starting at `entry`, passing the [`Pool`].
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn run(mut self, entry: EntryId) -> std::io::Result<(Self, Word)> {
        let label = &self.i[entry].label;
        let (lowerer, ret) = self.lowerer.execute(label, |f, pool| {
            let pool = pool.as_mut().as_mut_ptr();
            // Here is a good place to set a gdb breakpoint.
            f(pool)
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}
