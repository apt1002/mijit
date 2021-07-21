use std::num::{Wrapping};
use std::ops::{Index, IndexMut};

use crate::util::{AsUsize, ArrayMap};
use super::{code, optimizer};
use super::target::{Label, Counter, Word, Pool, Lower, Execute, Target, STATE_INDEX};
use code::{Variable, Action, Precision, Global, Convention};
use Precision::*;

/** Tracks the statistics for a [`Specialization`]. */
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    /** How often the fetch transition is executed. */
    pub fetches: u64,
    /** How often the retire transition is executed. */
    pub retires: u64,
    /** How often the specialization is visited. */
    pub visits: u64,
}

//-----------------------------------------------------------------------------

// Specialization
array_index! {
    /** Identifies a specialization of an `Engine`. */
    #[derive(Copy, Clone, Hash, PartialEq, Eq)]
    pub struct Specialization(std::num::NonZeroUsize) {
        debug_name: "Specialization",
        UInt: usize,
    }
}

/**
 * Tracks the relatives of a [`Specialization`].
 * See "doc/theory" for terminology.
 */
#[derive(Debug)]
struct Relatives {
    /** The fetch parent. `None` means the least specialization. */
    pub fetch_parent: Option<Specialization>,
    /** The retire parent. `None` means the least specialization. */
    pub retire_parent: Option<Specialization>,
    /** The fetch children. */
    pub fetch_children: Vec<Specialization>,
    /** The retire children. */
    pub retire_children: Vec<Specialization>,
}

/** Tracks the code compiled for a [`Specialization`]. */
struct Compiled {
    /** The equality test which must pass in order to execute `fetch`. */
    pub guard: Option<(Variable, u64)>,
    /** The fetch code that was compiled for this specialization. */
    pub fetch_code: Box<[Action]>,
    /**
     * The address just after `fetch_code`.
     * Retire children jump here.
     */
    pub fetch_label: Label,
    /**
     * The interface from `fetch_code` to `retire_code`.
     * Obeyed by children.
     */
    pub convention: Convention,
    /**
     * The address just before `retire_code`.
     * The last fetch child jumps here.
     */
    pub retire_label: Label,
    /** The retire code that was compiled for this specialization. */
    pub retire_code: Box<[Action]>,
    /**
     * The profiling counter for `retire_code`. Counts up to zero.
     * `retire_counter = [Statistics].retires - retire_threshold`.
     */
    pub retire_counter: Counter,
    /** The number of retire events at which we should interrupt the VM. */
    pub retire_threshold: Wrapping<u64>,
}

const DEFAULT_THRESHOLD_INCREMENT: u64 = 1000;

//-----------------------------------------------------------------------------

struct SpecializationInfo {
    pub relatives: Relatives,
    pub compiled: Compiled,
}

/**
 * This only exists to keep the borrow checker happy.
 * We might need to modify these fields while generating code.
 */
struct Internals {
    /**
     * The specializations in the order they were compiled, excluding the
     * least specialization. Indexed by [`Specialization`].
     */
    specializations: Vec<SpecializationInfo>,
    /**
     * Reached when a root specialization doesn't know what to do.
     * Can be viewed as the `fetch_label` of the least specialization.
     * We expect the caller to handle the situation then re-enter Mijit.
     */
    pub fetch_label: Label,
    /**
     * Reached if none of the root specializations' guards pass.
     * Can be viewed as the `retire_label` of the least specialization.
     * We return `-1` to the caller.
     */
    pub retire_label: Label,
}

impl Internals {
    /** Constructs a new specialization and informs its relatives. */
    fn new_specialization(
        &mut self,
        fetch_parent: Option<Specialization>,
        retire_parent: Option<Specialization>,
        compiled: Compiled,
    ) -> Specialization {
        let this = Specialization::new(self.specializations.len()).unwrap();
        if let Some(parent) = fetch_parent {
            self[parent].relatives.fetch_children.push(this);
        }
        if let Some(parent) = retire_parent {
            self[parent].relatives.retire_children.push(this);
        }
        let relatives = Relatives {
            fetch_parent: fetch_parent,
            retire_parent: retire_parent,
            fetch_children: Vec::new(),
            retire_children: Vec::new(),
        };
        self.specializations.push(SpecializationInfo {relatives, compiled});
        this
    }

    /** Returns an iterator through all the existing specializations. */
    fn all_specializations(&self) -> impl Iterator<Item=Specialization> + DoubleEndedIterator {
        (0..self.specializations.len()).map(|i| Specialization::new(i).unwrap())
    }

    /** Returns the `slots_used` of `s`, or of the least specialization. */
    fn slots_used(&self, s: Option<Specialization>) -> usize {
        s.map_or(0, |s| self[s].compiled.convention.slots_used)
    }

    /** Returns the `fetch_label` of `s`, or of the least specialization. */
    fn fetch_label_mut(&mut self, s: Option<Specialization>) -> &mut Label {
        match s {
            None => &mut self.fetch_label,
            Some(s) => &mut self[s].compiled.fetch_label,
        }
    }

    /** Returns the `retire_label` of `s`, or of the least specialization. */
    fn retire_label_mut(&mut self, s: Option<Specialization>) -> &mut Label {
        match s {
            None => &mut self.retire_label,
            Some(s) => &mut self[s].compiled.retire_label,
        }
    }
}

impl Index<Specialization> for Internals {
    type Output = SpecializationInfo;

    fn index(&self, s: Specialization) -> &Self::Output {
        &self.specializations[s.as_usize()]
    }
}

impl IndexMut<Specialization> for Internals {
    fn index_mut(&mut self, s: Specialization) -> &mut Self::Output {
        &mut self.specializations[s.as_usize()]
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
    /** The main entry point of the compiled code. */
    entry_point: Label,
    /** This nested struct can be borrowed independently of `lowerer`. */
    internals: Internals,
}

impl<T: Target> Engine<T> {
    pub fn new(target: T, num_globals: usize) -> Self {
        let pool = Pool::new(num_globals);
        let lowerer = target.lowerer(pool);
        let internals = Internals {
            specializations: Vec::new(),
            fetch_label: Label::new(None),
            retire_label: Label::new(None),
        };
        let entry_point = Label::new(None);
        Engine {_target: target, lowerer, entry_point, internals}._init()
    }

    fn _init(mut self) -> Self {
        let lo = &mut self.lowerer;
        // Assemble the function prologue and epilogue.
        lo.define(&mut self.entry_point);
        lo.prologue();
        lo.jump(&mut self.internals.retire_label);
        // Root specializations are inserted here.
        lo.define(&mut self.internals.retire_label);
        lo.action(Action::Constant(P32, STATE_INDEX, -1));
        lo.define(&mut self.internals.fetch_label);
        lo.epilogue();
        self
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        &mut self.lowerer.pool_mut()[global]
    }

    /** Returns an iterator through all the existing specializations. */
    #[allow(dead_code)]
    pub fn all_specializations(&self) -> impl Iterator<Item=Specialization> + DoubleEndedIterator {
        self.internals.all_specializations()
    }

    /**
     * The profiling subsystem interrupts execution of the VM when
     * [`Statistics.retires`] reaches a threshold value. When a
     * [`Specialization`] is constructed, and after each interrupt, it is
     * necessary to increment its threshold to rearm it.
     */
    fn increase_retire_threshold(&mut self, s: Specialization, increment: u64) {
        let increment = Wrapping(increment);
        let compiled = &mut self.internals[s].compiled;
        compiled.retire_threshold += increment;
        self.lowerer.pool_mut()[compiled.retire_counter] -= increment;
    }

    /**
     * Loop through all [`Specialization`]s and bring their [`Statistics`]
     * up to date.
     */
    #[allow(dead_code)]
    pub fn compute_statistics(&mut self) -> ArrayMap<Specialization, Statistics> {
        let mut ret: ArrayMap<_, Statistics> = ArrayMap::new(self.internals.specializations.len());
        for s in self.internals.all_specializations().rev() {
            // Read-only portion.
            let SpecializationInfo {relatives, compiled} = &self.internals[s];
            let child_fetches: u64 = relatives.fetch_children.iter().map(|&c| {
                assert!(c.as_usize() > s.as_usize());
                ret[c].fetches
            }).sum();
            let child_retires: u64 = relatives.retire_children.iter().map(|&c| {
                assert!(c.as_usize() > s.as_usize());
                ret[c].retires
            }).sum();
            // Write portion.
            let counter_value = self.lowerer.pool_mut()[compiled.retire_counter];
            let retires = (compiled.retire_threshold + counter_value).0;
            let visits = retires + child_fetches;
            let fetches = visits - child_retires;
            ret[s] = Statistics {fetches, retires, visits};
        }
        ret
    }

    /**
     * Compile code for a new [`Specialization`].
     * Unlike `compile()`, this method does not do any optimization. The caller
     * has control over `fetch_code`, `convention` and `retire_code`.
     */
    pub fn compile_inner(
        &mut self,
        fetch_parent: Option<Specialization>,
        retire_parent: Option<Specialization>,
        guard: Option<(Variable, u64)>,
        fetch_code: Box<[Action]>,
        convention: Convention,
        retire_code: Box<[Action]>,
    ) -> Specialization {
        let compiled = Compiled {
            guard,
            fetch_code,
            fetch_label: Label::new(None),
            convention,
            retire_label: Label::new(None),
            retire_code,
            retire_counter: self.lowerer.pool_mut().new_counter(),
            retire_threshold: Wrapping(0),
        };
        let this = self.internals.new_specialization(fetch_parent, retire_parent, compiled);
        let lo = &mut self.lowerer;
        *lo.slots_used() = self.internals.slots_used(fetch_parent);
        // Compile `guard`.
        let if_fail = self.internals.retire_label_mut(fetch_parent);
        lo.steal(if_fail, &mut lo.here());
        if let Some(guard) = guard {
            lo.test_eq(guard, if_fail);
        }
        { // Lifetime of `compiled` (can't touch `self.internals`).
            let compiled = &mut self.internals[this].compiled;
            // Compile `fetch_code`.
            for &action in compiled.fetch_code.iter() {
                lo.action(action);
            }
            lo.define(&mut compiled.fetch_label);
            lo.jump(&mut compiled.retire_label);
            // Compile `retire_code`.
            assert_eq!(*lo.slots_used(), compiled.convention.slots_used);
            lo.define(&mut compiled.retire_label);
            // TODO: Optimize the case where `retire_code` is empty.
            // The preceding jump should jump straight to `retire_parent`.
            for &action in compiled.retire_code.iter() {
                lo.action(action);
            }
            lo.count(compiled.retire_counter);
        }
        lo.jump(self.internals.fetch_label_mut(retire_parent));
        assert_eq!(*lo.slots_used(), self.internals.slots_used(retire_parent));
        this
    }

    /**
     * Compile code for a new [`Specialization`].
     *  - `guard` - the equality test which distinguishes the new
     *    `Specialization` from its fetch parent. The new `Specialization` will
     *    be reached only if its fetch parent is reached and `test_op` passes.
     *  - `actions` - the code that must be executed before retiring to the
     *    retire parent. This code will be optimized and divided between the
     *    `fetch_code` and `retire_code`.
     */
    pub fn compile(
        &mut self,
        fetch_parent: Specialization,
        retire_parent: Specialization,
        guard: Option<(Variable, u64)>,
        actions: &[Action],
    ) -> Specialization {
        let fetch_code = optimizer::optimize(
            self.lowerer.pool().num_globals(),
            &self.internals[fetch_parent].compiled.convention,
            &self.internals[retire_parent].compiled.convention,
            actions,
        );
        let this = self.compile_inner(
            Some(fetch_parent),
            Some(retire_parent),
            guard,
            fetch_code,
            self.internals[retire_parent].compiled.convention.clone(),
            Box::new([]),
        );
        self.increase_retire_threshold(this, DEFAULT_THRESHOLD_INCREMENT);
        this
    }

    /**
     * Constructs a new [`Specialization`] that provides a code path from
     * `fetch_parent` to `retire_parent` without going via their common parent.
     */
    #[allow(dead_code)]
    pub fn specialize(
        &mut self,
        fetch_parent: Specialization,
        retire_parent: Specialization,
    ) -> Specialization {
        assert_eq!(
            self.internals[retire_parent].relatives.fetch_parent,
            self.internals[fetch_parent].relatives.retire_parent,
        );
        let guard = self.internals[retire_parent].compiled.guard;
        let mut actions: Vec<_> = Vec::new();
        actions.extend(self.internals[fetch_parent].compiled.retire_code.iter().cloned());
        actions.extend(self.internals[retire_parent].compiled.fetch_code.iter().cloned());
        self.compile(fetch_parent, retire_parent, guard, &actions)
    }

    /**
     * Call the compiled code, passing the pool and `argument`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn execute(mut self, argument: Word) -> std::io::Result<(Self, Word)> {
        // FIXME: assert we are on x86_64 at compile time.
        let (lowerer, ret) = self.lowerer.execute(&self.entry_point, |f, pool| {
            let pool = pool.as_mut().as_mut_ptr();
            // Here is a good place to set a gdb breakpoint.
            f(pool, argument)
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}
