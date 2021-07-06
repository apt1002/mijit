use std::num::{Wrapping};
use std::ops::{Index, IndexMut};
use indexmap::{IndexSet};

use crate::util::{AsUsize, ArrayMap};
use super::{code, optimizer};
use super::target::{Label, Counter, Word, Pool, Lower, Execute, Target, STATE_INDEX};
use code::{Action, TestOp, Machine, Precision, Global, Value, FAST_VALUES};
use Precision::*;

/**
 * Represents the convention by which code passes values to a label. The
 * concept is similar to a calling convention, but it's for a jump, not a call.
 *
 * This is a place-holder. Possible future uses:
 *  - Register and spill-slot allocation, including dead values.
 *  - Knowledge about values, e.g. minimum and maximum possible value, and
 *    which bits are known to be set or clear.
 *  - Knowledge about possible common sub-expressions, e.g. knowing that some
 *    value is the difference of two other values.
 *  - Knowledge about the cache state, e.g. that some value is the value of
 *    some memory location, and whether it needs to be stored.
 */
#[derive(Debug, Clone)]
pub struct Convention {
    /** The Value that will be tested next. */
    // pub discriminant: Value,
    /** The values that are live on entry, including `discriminant`. */
    pub live_values: Vec<Value>,
    /**
     * The number of spill [`Slot`]s used by the Convention.
     *
     * [`Slot`]: code::Slot
     */
    pub slots_used: usize,
}

//-----------------------------------------------------------------------------

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
    /** Identifies a specialization of a `Jit`. */
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
    pub _fetch_parent: Option<Specialization>,
    /** The retire parent. `None` means the least specialization. */
    pub _retire_parent: Option<Specialization>,
    /** The fetch children. */
    pub fetch_children: Vec<Specialization>,
    /** The retire children. */
    pub retire_children: Vec<Specialization>,
}

/** Tracks the code compiled for a [`Specialization`]. */
struct Compiled {
    /** The test which must pass in order to execute `fetch`. */
    pub _guard: (TestOp, Precision),
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
            _fetch_parent: fetch_parent,
            _retire_parent: retire_parent,
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
 * The state of the JIT compiler. This includes the memory allocated for the
 * compiled code, and all house-keeping data.
 */
#[allow(clippy::module_name_repetitions)]
pub struct JitInner<T: Target> {
    /** The compilation target. */
    _target: T,
    /** The code compiled so far. */
    lowerer: T::Lowerer,
    /** The main entry point of the compiled code. */
    entry_point: Label,
    /** This nested struct can be borrowed independently of `lowerer`. */
    internals: Internals,
}

impl<T: Target> JitInner<T> {
    pub fn new(target: T, num_globals: usize) -> Self {
        let pool = Pool::new(num_globals);
        let lowerer = target.lowerer(pool);
        let internals = Internals {
            specializations: Vec::new(),
            fetch_label: Label::new(None),
            retire_label: Label::new(None),
        };
        let entry_point = Label::new(None);
        JitInner {_target: target, lowerer, entry_point, internals}._init()
    }

    fn _init(mut self) -> Self {
        let lo = &mut self.lowerer;
        // Assemble the function prologue and epilogue.
        lo.define(&mut self.entry_point);
        lo.lower_prologue();
        lo.jump(&mut self.internals.retire_label);
        // Root specializations are inserted here.
        lo.define(&mut self.internals.retire_label);
        lo.lower_action(Action::Constant(P32, STATE_INDEX, -1));
        lo.define(&mut self.internals.fetch_label);
        lo.lower_epilogue();
        self
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        &mut self.lowerer.pool_mut()[global]
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
        guard: (TestOp, Precision),
        fetch_code: Box<[Action]>,
        convention: Convention,
        retire_code: Box<[Action]>,
    ) -> Specialization {
        let compiled = Compiled {
            _guard: guard,
            fetch_code: fetch_code,
            fetch_label: Label::new(None),
            convention,
            retire_label: Label::new(None),
            retire_code: retire_code,
            retire_counter: self.lowerer.pool_mut().new_counter(),
            retire_threshold: Wrapping(0),
        };
        let this = self.internals.new_specialization(fetch_parent, retire_parent, compiled);
        let lo = &mut self.lowerer;
        *lo.slots_used() = self.internals.slots_used(fetch_parent);
        // Compile `guard`.
        let if_fail = self.internals.retire_label_mut(fetch_parent);
        lo.steal(&mut lo.here(), if_fail);
        lo.lower_test_op(guard, if_fail);
        { // Lifetime of `compiled` (can't touch `self.internals`).
            let compiled = &mut self.internals[this].compiled;
            // Compile `fetch_code`.
            for &action in compiled.fetch_code.iter() {
                lo.lower_action(action);
            }
            lo.define(&mut compiled.fetch_label);
            lo.jump(&mut compiled.retire_label);
            // Compile `retire_code`.
            assert_eq!(*lo.slots_used(), compiled.convention.slots_used);
            lo.define(&mut compiled.retire_label);
            // TODO: Optimize the case where `retire_code` is empty.
            // The preceding jump should jump straight to `retire_parent`.
            for &action in compiled.retire_code.iter() {
                lo.lower_action(action);
            }
            lo.lower_count(compiled.retire_counter);
        }
        lo.jump(self.internals.fetch_label_mut(retire_parent));
        assert_eq!(*lo.slots_used(), self.internals.slots_used(retire_parent));
        this
    }

    /**
     * Compile code for a new [`Specialization`].
     *  - `guard` - the boolean test which distinguishes the new
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
        guard: (TestOp, Precision),
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
            // Here is a good place to set a gdb breakpoint.
            f(pool.as_mut().as_mut_ptr(), argument)
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}

//-----------------------------------------------------------------------------

/** The state of the JIT compiler for a [`Machine`]. */
pub struct Jit<M: Machine, T: Target> {
    /** The low-level bookkeeping data structures. */
    inner: JitInner<T>,
    /** The [`Machine`]. */
    machine: M,
    /**
     * Numbering of all [`M::State`]s.
     *
     * [`M::State`]: Machine::State
     */
    states: IndexSet<M::State>,
    /**
     * The [`Specialization`] corresponding to each [`M::State`].
     *
     * [`M::State`]: Machine::State
     */
    roots: Vec<Specialization>,
}

impl<M: Machine, T: Target> Jit<M, T> {
    pub fn new(machine: M, target: T) -> Self {
        // Construct the `JitInner`.
        let inner = JitInner::new(target, machine.num_globals());

        // Construct the Jit.
        let states = IndexSet::new();
        let roots = Vec::new();
        let mut jit = Jit {inner, machine, states, roots};

        // Enumerate the reachable states in FIFO order and
        // construct the control-flow graph of the `Machine`.
        for state in jit.machine.initial_states() {
            jit.ensure_root(state);
        }
        let mut done = 0;
        while let Some(old_state) = jit.states.get_index(done).cloned() {
            let cases = jit.machine.code(old_state.clone());
            for case in cases {
                jit.ensure_root(case.new_state.clone());
                jit.compile(&old_state, case.condition, &case.actions, &case.new_state);
            }
            done += 1;
        }

        jit
    }

    pub fn states(&self) -> &IndexSet<M::State> {
        &self.states
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        self.inner.global_mut(global)
    }

    /** Ensure there is a root [`Specialization`] for `state`. */
    pub fn ensure_root(&mut self, state: M::State) {
        let index = self.roots.len();
        assert_eq!(index, self.states.len());
        if self.states.insert(state.clone()) {
            // Make a new root `Specialization`.
            let mask = self.machine.liveness_mask(state);
            let live_values: Vec<Value> = (0..FAST_VALUES.len())
                .filter(|i| (mask & (1 << i)) != 0)
                .map(|i| FAST_VALUES[i])
                .chain((0..self.machine.num_globals()).map(|i| Global(i).into()))
                .collect();
            let slots_used = self.machine.num_slots();
            assert_eq!(slots_used & 1, 0);
            let mut fetch_code: Vec<Action> = (0..(slots_used >> 1)).map(
                |_| Action::Push(None, None)
            ).collect();
            fetch_code.extend(self.machine.prologue());
            let mut retire_code = self.machine.epilogue();
            retire_code.push(Action::DropMany(slots_used >> 1));
            retire_code.push(Action::Constant(P32, STATE_INDEX, index as i64));
            self.roots.push(self.inner.compile_inner(
                None,
                None,
                (TestOp::Eq(STATE_INDEX.into(), index as i32), P32),
                fetch_code.into(),
                Convention {live_values, slots_used},
                retire_code.into(),
            ));
        }
    }

    /**
     * Insert a control-flow arc from `old_state` to `new_state` with the
     * specified `guard` and `actions`.
     */
    pub fn compile(
        &mut self,
        old_state: &M::State,
        guard: (TestOp, Precision),
        actions: &[Action],
        new_state: &M::State,
    ) -> Specialization {
        self.inner.compile(
            self.roots[self.states.get_index_of(old_state).unwrap()],
            self.roots[self.states.get_index_of(new_state).unwrap()],
            guard,
            actions,
        )
    }

    /**
     * Call the compiled code, starting in `state`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn execute(mut self, state: &M::State) -> std::io::Result<(Self, M::State)> {
        let index = self.states.get_index_of(state).expect("invalid state");
        let index = Word {u: index as u64};
        let (inner, new_index) = self.inner.execute(index)?;
        let new_index = new_index.u as usize;
        self.inner = inner;
        let new_state = self.states.get_index(new_index).expect("invalid index").clone();
        Ok((self, new_state))
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod factorial;

#[cfg(test)]
pub mod tests {
    use super::*;

    use std::convert::{TryFrom};

    use super::super::target::{Word, native};

    #[test]
    pub fn factorial() {
        use factorial::*;
        use State::*;

        let mut jit = Jit::new(Machine, native());

        // Check the `states` list.
        let expected: IndexSet<_> = vec![
            Start, Loop, Return,
        ]
        .into_iter()
        .collect();
        assert_eq!(jit.states(), &expected);

        // Run some "code".
        *jit.global_mut(Global::try_from(reg::N).unwrap()) = Word {u: 5};
        let (mut jit, final_state) = unsafe {
            jit.execute(&Start).expect("Execute failed")
        };
        assert_eq!(final_state, Return);
        assert_eq!(*jit.global_mut(Global::try_from(reg::RESULT).unwrap()), Word {u: 120});

        // Check profiling counter.
        let expected = vec![
            Statistics {fetches: 1, retires: 0, visits: 1},
            Statistics {fetches: 0, retires: 0, visits: 6},
            Statistics {fetches: 1, retires: 1, visits: 1},
            Statistics {fetches: 0, retires: 1, visits: 1},
            Statistics {fetches: 1, retires: 1, visits: 1},
            Statistics {fetches: 5, retires: 5, visits: 5},
        ];
        let observed = jit.inner.compute_statistics();
        for (s, expected) in jit.inner.internals.all_specializations().zip(&expected) {
            assert_eq!(expected, &observed[s]);
        }
    }
}
