use std::ops::{Index, IndexMut};

use crate::util::{AsUsize};
use super::target::{Label, Word, Pool, Lower, Execute, Target, RESULT};
use super::code::{Precision, Global, Switch, Action, Convention, Marshal, Propagator, EBB, Ending};
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
 * `Case`, as must `convention` (they can all be `None` during construction).
 */
#[derive(Debug)]
struct Case {
    /** The unique [`Switch`] that can jump directly to this `Case`. */
    fetch_parent: Option<CaseId>,
    /** The [`Convention`] on entry (i.e. at `label`). */
    before: Option<Convention>,
    /** The address of the code. */
    label: Label,
    /** The `Retire`, if any. */
    retire: Option<Retire>,
    /** The `Fetch`, if any. */
    fetch: Option<Fetch>,
}

impl Case {
    pub fn convention(&self) -> &Convention {
        assert!(self.retire.is_some() || self.fetch.is_some());
        self.before.as_ref().expect("Incompletely constructed")
    }

    /**
     * If `self.before` is `None`, replaces it with `new`.
     * Otherwise, assert that `new` refines `self.before`.
     */
    fn set_convention(&mut self, new: Convention) {
        if let Some(old) = &self.before {
            assert!(new.refines(old));
        } else {
            self.before = Some(new);
        }
    }
}

//-----------------------------------------------------------------------------

/**
 * This only exists to keep the borrow checker happy.
 * We might need to borrow these fields while generating code.
 */
#[derive(Debug)]
struct Internals {
    /** The [`Convention`] obeyed by the root. */
    convention: Convention,
    /**
     * The [`Case`]s in the order they were compiled, excluding the root.
     * Indexed by [`CaseId`].
     */
    cases: Vec<Case>,
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
    fn new_case(&mut self, fetch_parent: impl Into<Option<CaseId>>) -> CaseId {
        let id = CaseId::new(self.cases.len()).unwrap();
        self.cases.push(Case {
            fetch_parent: fetch_parent.into(),
            before: None,
            label: Label::new(None),
            retire: None,
            fetch: None,
        });
        id
    }

    /** Find the [`Convention`] for a [`CaseId`] allowing for `None`. */
    fn convention(&self, id: impl Into<Option<CaseId>>) -> &Convention {
        id.into().map_or(&self.convention, |id| self[id].convention())
    }

    /**
     * Add a [`Retire`] to a [`Case`] that doesn't have a [`Fetch`].
     */
    fn add_retire(&mut self, lo: &mut impl Lower, id: CaseId, retire: Retire) {
        assert!(self[id].fetch.is_none());
        // Compute the `before` convention.
        let mut propagator = Propagator::new(self.convention(retire.jump));
        for &action in retire.actions.iter().rev() {
            propagator.action(action);
        }
        let before = propagator.before();
        *lo.slots_used_mut() = before.slots_used;
        // Intercept all jumps to `id`.
        let mut here = lo.here();
        lo.steal(&mut self[id].label, &mut here);
        self[id].label = here;
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
        self[id].set_convention(before);
        self[id].retire = Some(retire);
    }

    /**
     * Add a [`Fetch`] to a [`Case`] that doesn't have one.
     *
     * Every child `Case` must have `id` as its `fetch_parent`.
     */
    fn add_fetch(&mut self, lo: &mut impl Lower, id: CaseId, fetch: Fetch) {
        assert!(self[id].fetch.is_none());
        // Compute the `before` convention.
        let mut propagator = Propagator::switch(&fetch.switch, |&child| self[child].convention());
        for &action in fetch.actions.iter().rev() {
            propagator.action(action);
        }
        if self[id].retire.is_some() {
            propagator.branch(self[id].convention());
        }
        let before = propagator.before();
        *lo.slots_used_mut() = before.slots_used;
        // Intercept all jumps to `id`.
        let mut here = lo.here();
        lo.steal(&mut self[id].label, &mut here);
        self[id].label = here;
        // Compile `fetch`.
        lo.actions(&*fetch.actions);
        let slots_used = *lo.slots_used_mut();
        let check_child = |child: &Case| {
            assert_eq!(child.convention().slots_used, slots_used);
            assert_eq!(child.fetch_parent, Some(id));
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
        self[id].set_convention(before);
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

impl<T: Target> std::fmt::Debug for Engine<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("Engine")
            .field("cases", &self.i.cases)
            .finish()
    }
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
            convention: Convention::empty(num_globals),
            cases: Vec::new(),
        };
        Engine {_target: target, lowerer, i}
    }

    /** Borrows the value of variable `global`. */
    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        &mut self.lowerer.pool_mut()[global]
    }

    /**
     * Define the code for case `id`.
     *
     *  - id - the case to modify.
     *  - ebb - the extended basic block defining the desired behaviour.
     *  - to_case - called for every leaf of the EBB to determine where to
     *    jump to.
     */
    pub fn build<L: Clone>(
        &mut self,
        id: CaseId,
        ebb: &EBB<L>,
        to_case: &impl Fn(L) -> CaseId,
    ) {
        let ebb_actions = ebb.actions.iter().copied().collect();
        match &ebb.ending {
            Ending::Leaf(leaf) => {
                let jump = to_case(leaf.clone());
                self.i.add_retire(&mut self.lowerer, id, Retire {actions: ebb_actions, jump: Some(jump)});
            },
            Ending::Switch(switch) => {
                let switch = switch.map(|child_ebb| {
                    let child = self.i.new_case(Some(id));
                    self.build(child, child_ebb, to_case);
                    child
                });
                self.i.add_fetch(&mut self.lowerer, id, Fetch {actions: ebb_actions, switch});
            },
        }
    }

    /**
     * Construct an entry to this [`Engine`]. Initially, the code at the
     * entry will immediately return `exit_value`. To change this behaviour,
     * use [`build()`].
     *
     *  - marshal.prologue - executed on every entry to the compiled code.
     *  - marshal.epilogue - executed on every exit from the compiled code.
     *  - exit_value - returned to the caller on exit. Must be non-negative.
     *
     * Returns:
     *  - label - the external entry point, which can be passed to `run()`.
     *  - id - the `CaseId` corresponding to the entry.
     */
    pub fn new_entry(&mut self, marshal: &Marshal, exit_value: i64) -> (Label, CaseId) {
        assert!(exit_value >= 0);
        let id = self.i.new_case(None);
        // Compile the epilogue.
        let mut actions = Vec::new();
        actions.extend(marshal.epilogue.iter().copied());
        actions.push(Action::Constant(P64, RESULT, exit_value));
        self.i.add_retire(&mut self.lowerer, id, Retire {actions: actions.into(), jump: None});
        // Compile the prologue.
        let lo = &mut self.lowerer;
        *lo.slots_used_mut() = 0;
        let label = lo.here();
        lo.prologue();
        lo.actions(&marshal.prologue);
        assert_eq!(*lo.slots_used_mut(), self.i[id].convention().slots_used);
        lo.jump(&mut self.i[id].label);
        // Return.
        (label, id)
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
                    Switch::Always(jump) => {
                        // Loop.
                        id = **jump;
                        continue;
                    },
                    switch => {
                        // Succeed.
                        return Some(EBB {
                            actions: actions.into(),
                            ending: Ending::Switch(switch.map(|&jump| EBB {
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
    #[allow(unused)] // TODO.
    fn specialize(&mut self, id: CaseId) {
        assert!(self.i[id].fetch.is_none());
        if let Some(ebb) = self.hot_path(id) {
            // TODO: Optimize `ebb`.
            self.build(id, &ebb, &|c| c);
        }
    }

    /**
     * Call the compiled code starting at `label`, passing the [`Pool`].
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code is invalid.
     */
    pub unsafe fn run(mut self, label: &Label) -> std::io::Result<(Self, Word)> {
        let (lowerer, ret) = self.lowerer.execute(label, |f, pool| {
            let pool = pool.as_mut().as_mut_ptr();
            // Here is a good place to set a gdb breakpoint.
            f(pool)
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}
