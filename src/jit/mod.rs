use std::ops::{Index, IndexMut};
use indexmap::{IndexSet};

use crate::util::{AsUsize};
use super::{code, optimizer};
use super::target::{Label, Word, Pool, Lowerer, Execute, Target, STATE_INDEX};
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

/**
 * The type of the generated code.
 *  - `current_index` - the index of the current `M::State` in `states`.
 * Returns:
 *  - `new_index` - updated `current_index`.
 */
type RunFn = extern "C" fn(
    /* pool */ *mut Word,
    /* current_index */ usize,
) -> /* new_index */ usize;

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
    pub _fetch_code: Box<[Action]>,
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
    pub _retire_code: Box<[Action]>,
}

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

    /** Returns the `slots_used` of `s`, or of the least specialization. */
    fn slots_used(&self, s: Option<Specialization>) -> usize {
        s.map_or(0, |s| self[s].compiled.convention.slots_used)
    }

    /** Returns the `fetch_label` of `s`, or of the least specialization. */
    fn fetch_label(&mut self, s: Option<Specialization>) -> &mut Label {
        match s {
            None => &mut self.fetch_label,
            Some(s) => &mut self[s].compiled.fetch_label,
        }
    }

    /** Returns the `retire_label` of `s`, or of the least specialization. */
    fn retire_label(&mut self, s: Option<Specialization>) -> &mut Label {
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
    pub fn new(target: T, code_size: usize, num_globals: usize) -> Self {
        let pool = Pool::new(num_globals);
        let lowerer = target.lowerer(pool, code_size);
        let internals = Internals {
            specializations: Vec::new(),
            fetch_label: Label::new(),
            retire_label: Label::new(),
        };
        let entry_point = Label::new();
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
        let lo = &mut self.lowerer;
        *lo.slots_used() = self.internals.slots_used(fetch_parent);
        let mut fetch_label = Label::new();
        let mut retire_label = Label::new();
        let if_fail = self.internals.retire_label(fetch_parent);
        *if_fail = lo.patch(if_fail);
        lo.lower_test_op(guard, if_fail);
        for &action in fetch_code.iter() {
            lo.lower_action(action);
        }
        lo.define(&mut fetch_label);
        lo.jump(&mut retire_label);
        assert_eq!(*lo.slots_used(), convention.slots_used);
        lo.define(&mut retire_label);
        // TODO: Optimize the case where `retire_code` is empty.
        // The preceding jump should jump straight to `retire_parent`.
        for &action in retire_code.iter() {
            lo.lower_action(action);
        }
        lo.jump(self.internals.fetch_label(retire_parent));
        assert_eq!(*lo.slots_used(), self.internals.slots_used(retire_parent));
        let compiled = Compiled {
            _guard: guard,
            _fetch_code: fetch_code,
            fetch_label,
            convention,
            retire_label,
            _retire_code: retire_code,
        };
        self.internals.new_specialization(fetch_parent, retire_parent, compiled)
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
        self.compile_inner(
            Some(fetch_parent),
            Some(retire_parent),
            guard,
            fetch_code,
            self.internals[retire_parent].compiled.convention.clone(),
            Box::new([]),
        )
    }

    /**
     * Call the compiled code, passing the pool and `argument`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn execute(mut self, argument: usize) -> std::io::Result<(Self, usize)> {
        // FIXME: assert we are on x86_64 at compile time.
        let (lowerer, ret) = self.lowerer.execute(&self.entry_point, |bytes, pool| {
            let f: RunFn = unsafe { std::mem::transmute(&bytes[0]) };
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
    pub fn new(machine: M, target: T, code_size: usize) -> Self {
        // Construct the `JitInner`.
        let inner = JitInner::new(target, code_size, machine.num_globals());

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
            let mut fetch_code: Vec<Action> = (0..slots_used).map(
                |_| Action::Push(FAST_VALUES[0]) // TODO: Make one instruction.
            ).collect();
            fetch_code.extend(self.machine.prologue());
            let mut retire_code = self.machine.epilogue();
            retire_code.push(Action::DropMany(slots_used));
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
        let (inner, new_index) = self.inner.execute(index)?;
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

    use super::super::target::{native};

    /** An amount of code space suitable for running tests. */
    pub const CODE_SIZE: usize = 1 << 20;

    #[test]
    pub fn factorial() {
        use factorial::*;
        use State::*;

        let mut jit = Jit::new(Machine, native(), CODE_SIZE);

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
    }
}
