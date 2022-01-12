use std::ops::{Index, IndexMut};

use crate::util::{AsUsize};
use super::{code};
use super::target::{Label, Word, Pool, Lower, Execute, Target, RESULT};
use code::{Precision, Global, Switch, Action, Convention, Marshal, EBB, Ending};
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
 *
 * One or both of `fetch` and `retire` must be non-`None` for every reachable
 * `Case` (they can both be `None` during construction).
 */
#[derive(Debug)]
struct Case {
    /** The unique [`Switch`] that can jump directly to this `Case`. */
    fetch_parent: Option<CaseId>,
    /** The [`Convention`] on entry (i.e. at `label`). */
    convention: Convention,
    /** The address of the code. */
    label: Label,
    /** The `Retire`, if any. */
    retire: Option<Retire>,
    /** The `Fetch`, if any. */
    fetch: Option<Fetch>,
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
    /**
     * Constructs a new [`Case`], initially with an undefined `label` and with
     * neither a [`Retire`] nor a [`Fetch`]. Call at least one of
     * `add_retire()` and `add_fetch()` before using the new `Case`.
     *  - fetch_parent - the `Case` whose `Fetch` will eventually jump to the
     *    new `Case`.
     *  - convention - the [`Convention`] in effect on entry to the new `Case`.
     */
    fn new_case(&mut self, fetch_parent: impl Into<Option<CaseId>>, convention: Convention) -> CaseId {
        let id = CaseId::new(self.cases.len()).unwrap();
        self.cases.push(Case {
            fetch_parent: fetch_parent.into(),
            convention,
            label: Label::new(None),
            retire: None,
            fetch: None,
        });
        id
    }

    /** Constructs a new `Entry` that wraps `case`. */
    fn new_entry(&mut self, label: Label, case: CaseId) -> EntryId {
        let id = EntryId::new(self.entries.len()).unwrap();
        self.entries.push(Entry {label, case});
        id
    }

    /** Find the [`Convention`] for a [`CaseId`] allowing for `None`. */
    fn convention(&self, id: impl Into<Option<CaseId>>) -> &Convention {
        id.into().map_or(&self.convention, |id| &self[id].convention)
    }

    /**
     * Add a [`Retire`] to a [`Case`] that doesn't have one, and that also
     * doesn't have a [`Fetch`].
     *
     * The [`Convention`] of `retire.jump` must be compatible with the
     * situation after executing `retire.actions`.
     */
    fn add_retire(&mut self, lo: &mut impl Lower, id: CaseId, retire: Retire) {
        assert!(self[id].retire.is_none());
        assert!(self[id].fetch.is_none());
        *lo.slots_used_mut() = self[id].convention.slots_used;
        // Intercept all jumps to `id`.
        lo.define(&mut self[id].label);
        // Compile `retire`.
        lo.actions(&*retire.actions);
        let slots_used = *lo.slots_used_mut();
        assert_eq!(self.convention(retire.jump).slots_used, slots_used);
        if let Some(jump) = retire.jump {
            // Jump to a non-root `Case`.
            lo.jump(&mut self[jump].label);
        } else {
            // Jump to the root.
            lo.epilogue()
        }
        self[id].retire = Some(retire);
    }

    /**
     * Add a [`Fetch`] to a [`Case`] that doesn't have one.
     *
     * Every child `Case` must have `id` as its `fetch_parent`, and its
     * [`Convention`] must be compatible with the situation after executing
     * `fetch.actions`.
     */
    fn add_fetch(&mut self, lo: &mut impl Lower, id: CaseId, fetch: Fetch) {
        assert!(self[id].fetch.is_none());
        *lo.slots_used_mut() = self[id].convention.slots_used;
        // Intercept all jumps to `id`.
        let mut here = lo.here();
        lo.steal(&mut self[id].label, &mut here);
        self[id].label = here;
        // Compile `fetch`.
        lo.actions(&*fetch.actions);
        let slots_used = *lo.slots_used_mut();
        let check_child = |child: &Case| {
            assert_eq!(child.convention.slots_used, slots_used);
            assert_eq!(child.fetch_parent, Some(id));
            assert!(child.retire.is_some() || child.fetch.is_some());
        };
        match fetch.switch {
            Switch::Index {discriminant, ref cases, ref default_} => {
                for (index, &case) in cases.iter().enumerate() {
                    check_child(&self[case]);
                    lo.if_eq((discriminant, index as u64), &mut self[case].label);
                }
                check_child(&self[**default_]);
                lo.jump(&mut self[**default_].label);
            },
            Switch::Always(ref jump) => {
                check_child(&self[**jump]);
                lo.jump(&mut self[**jump].label);
            },
        }
        self[id].fetch = Some(fetch);
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

    /**
     * Recursively constructs a tree of [`Case`]s that implements an [`EBB`].
     * `root` will acquire a [`Retire`] or a [`Fetch`] depending on whether
     * `ending` is an [`Ending::Leaf`] or an [`Ending::Switch`].
     */
    // TODO: Make private. Revealing it suppresses several "unused" warnings.
    pub fn build(&mut self, root: CaseId, actions: Box<[Action]>, ending: &Ending<CaseId>) {
        match ending {
            Ending::Leaf(jump) => {
                self.i.add_retire(&mut self.lowerer, root, Retire {actions, jump: Some(*jump)});
            },
            Ending::Switch(switch) => {
                let switch = switch.map(|EBB {before, actions, ending}| {
                    let id = self.i.new_case(Some(root), before.clone());
                    let actions = actions.iter().copied().collect();
                    self.build(id, actions, ending);
                    id
                });
                self.i.add_fetch(&mut self.lowerer, root, Fetch {actions, switch});
            },
        }
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
        let case = self.i.new_case(None, marshal.convention.clone());
        // Compile the epilogue.
        let mut actions = Vec::new();
        actions.extend(marshal.epilogue.iter().copied());
        actions.push(Action::Constant(P64, RESULT, exit_value));
        self.i.add_retire(&mut self.lowerer, case, Retire {actions: actions.into(), jump: None});
        // Compile the prologue.
        let lo = &mut self.lowerer;
        *lo.slots_used_mut() = 0;
        let label = lo.here();
        lo.prologue();
        lo.actions(&marshal.prologue);
        assert_eq!(*lo.slots_used_mut(), self.i[case].convention.slots_used);
        lo.jump(&mut self.i[case].label);
        // Wrap and return.
        self.i.new_entry(label, case)
    }

    /** Tests whether [`define(entry, ...)`] has been called. */
    pub fn is_defined(&self, entry: EntryId) -> bool {
        self.i[self.i[entry].case].fetch.is_some()
    }

    /**
     * Replace the code at `entry` such that it executes `actions` and then
     * jumps to the [`EntryId`] selected by `switch`. Each `EntryId` may only
     * be defined once.
     */
    pub fn define(&mut self, entry: EntryId, actions: Box<[Action]>, switch: &Switch<EntryId>) {
        assert!(!self.is_defined(entry));
        let switch = Ending::Switch(switch.map(|&e: &EntryId| {
            let jump = self.i[e].case;
            EBB {
                before: self.i.convention(jump).clone(),
                actions: Vec::new(),
                ending: Ending::Leaf(jump),
            }
        }));
        self.build(self.i[entry].case, actions, &switch);
    }

    /**
     * Returns a copy of the hot path starting at `id` up to the next
     * [`Switch`]. Returns `None` if the hot path exits Mijit without reaching
     * a `Switch`.
     */
    fn hot_path(&self, mut id: CaseId) -> Option<EBB<CaseId>> {
        let mut actions = Vec::new();
        loop {
            if let Some(fetch) = &self.i[id].fetch {
                actions.extend(fetch.actions.iter().copied());
                match &fetch.switch {
                    Switch::Always(ref jump) => {
                        // Loop.
                        id = **jump;
                        continue;
                    },
                    switch => {
                        // Succeed.
                        return Some(EBB {
                            before: self.i.convention(id).clone(),
                            actions: actions.into(),
                            ending: Ending::Switch(switch.map(|&jump| EBB {
                                before: self.i.convention(jump).clone(),
                                actions: Vec::new(),
                                ending: Ending::Leaf(jump),
                            })),
                        });
                    },
                }
            }
            if let Some(retire) = &self.i[id].retire {
                actions.extend(retire.actions.iter().copied());
                if let Some(jump) = retire.jump {
                    // Loop.
                    id = jump;
                    continue;
                } else {
                    // Fail.
                    return None;
                }
            }
            panic!("Case has neither Fetch nor Retire");
        }
    }

    /**
     * Find the hot path starting at `id`, which must be a [`Retire`].
     * Clone it, optimize it, and replace `id` with a [`Fetch`].
     */
    // TODO: Make private. Revealing it suppresses several "unused" warnings.
    pub fn specialize(&mut self, id: CaseId) {
        assert!(self.i[id].fetch.is_none());
        if let Some(ebb) = self.hot_path(id) {
            // TODO: Optimize `ebb`.
            self.build(id, ebb.actions.into(), &ebb.ending);
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
