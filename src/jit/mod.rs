use indexmap::{IndexSet};

use crate::util::{AsUsize};
use super::{code, optimizer};
use super::target::{Label, Lowerer, Target, STATE_INDEX};
use code::{Action, TestOp, Machine, Precision, Global, Slot, Value, IntoValue, FAST_VALUES};
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
    /** The number of spill [`Slot`]s used by the Convention. */
    pub slots_used: usize,
}

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

/**
 * The type of the generated code.
 *  - `current_index` - the index of the current `M::State` in `states`.
 * Returns:
 *  - `new_index` - updated `current_index`.
 */
type RunFn = extern "C" fn(
    /* pool */ *mut u64,
    /* current_index */ usize,
) -> /* new_index */ usize;

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
    specializations: Vec<(Relatives, Compiled)>,
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
            self.specializations[parent.as_usize()].0.fetch_children.push(this);
        }
        if let Some(parent) = retire_parent {
            self.specializations[parent.as_usize()].0.retire_children.push(this);
        }
        let relatives = Relatives {
            _fetch_parent: fetch_parent,
            _retire_parent: retire_parent,
            fetch_children: Vec::new(),
            retire_children: Vec::new(),
        };
        self.specializations.push((relatives, compiled));
        this
    }

    /** Returns the `convention` of `s`. */
    fn convention(&self, s: Specialization) -> &Convention {
        &self.specializations[s.as_usize()].1.convention
    }

    /** Returns the `fetch_label` of `s`, or of the least specialization. */
    fn fetch_label(&mut self, s: Option<Specialization>) -> &mut Label {
        match s {
            None => &mut self.fetch_label,
            Some(s) => &mut self.specializations[s.as_usize()].1.fetch_label,
        }
    }

    /** Returns the `retire_label` of `s`, or of the least specialization. */
    fn retire_label(&mut self, s: Option<Specialization>) -> &mut Label {
        match s {
            None => &mut self.retire_label,
            Some(s) => &mut self.specializations[s.as_usize()].1.retire_label,
        }
    }
}

/**
 * The state of the JIT compiler. This includes the memory allocated for the
 * compiled code, and all house-keeping data.
 */
#[allow(clippy::module_name_repetitions)]
pub struct JitInner<T: Target> {
    /** The compilation target. */
    target: T,
    /** The code compiled so far. */
    lowerer: T::Lowerer,
    /** This nested struct can be borrowed independently of `lowerer`. */
    internals: Internals,
    /** The pool of mutable storage locations. */
    pool: Vec<u64>,
}

impl<T: Target> JitInner<T> {
    pub fn new(target: T, code_size: usize, num_globals: usize) -> Self {
        let lowerer = target.lowerer(num_globals, code_size);
        let internals = Internals {
            specializations: Vec::new(),
            fetch_label: Label::new(),
            retire_label: Label::new(),
        };
        // FIXME: replace "1000" by dynamically-calculated value.
        let pool = vec![0; num_globals + 1 + 1000];
        JitInner {target, lowerer, internals, pool}._init()
    }

    fn _init(mut self) -> Self {
        let lo = &mut self.lowerer;
        // Assemble the function prologue and epilogue.
        lo.lower_prologue();
        lo.jump(&mut self.internals.retire_label);
        // Root specializations are inserted here.
        lo.define(&mut self.internals.retire_label);
        lo.lower_action(Action::Constant(P32, STATE_INDEX, -1));
        lo.define(&mut self.internals.fetch_label);
        lo.lower_epilogue();
        self
    }

    // TODO: Take a `Global`, not a `Value`.
    pub fn global(&mut self, global: impl IntoValue) -> &mut u64 {
        match global.into() {
            // TODO: Factor out pool index calculation.
            Value::Global(Global(index)) => &mut self.pool[index + 1],
            _ => panic!("Not a Global"),
        }
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
        lo.define(&mut retire_label);
        // TODO: Optimize the case where `retire_code` is empty.
        // The preceding jump should jump straight to `retire_parent`.
        for &action in retire_code.iter() {
            lo.lower_action(action);
        }
        lo.jump(self.internals.fetch_label(retire_parent));
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
            self.lowerer.num_globals(),
            self.internals.convention(fetch_parent),
            self.internals.convention(retire_parent),
            actions,
        );
        self.compile_inner(
            Some(fetch_parent),
            Some(retire_parent),
            guard,
            fetch_code,
            self.internals.convention(retire_parent).clone(),
            Box::new([]),
        )
    }

    /**
     * Call the compiled code, passing the pool and `argument`.
     * - bytes - the compiled code.
     */
    pub fn execute(mut self, argument: usize) -> std::io::Result<(Self, usize)> {
        // FIXME: assert we are on x86_64 at compile time.
        let pool = self.pool.as_mut_ptr();
        let (lowerer, ret) = self.target.execute(self.lowerer, |bytes| {
            let f: RunFn = unsafe { std::mem::transmute(&bytes[0]) };
            // Here is a good place to set a gdb breakpoint.
            f(pool, argument)
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

    pub fn global(&mut self, global: impl IntoValue) -> &mut u64 {
        self.inner.global(global)
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
            let slots_used = live_values.iter().fold(0, |acc, &v| {
                match v {
                    Value::Slot(Slot(index)) => std::cmp::max(acc, index + 1),
                    _ => acc,
                }
            });
            let fetch_code = self.machine.prologue();
            let mut retire_code = self.machine.epilogue();
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

    pub fn execute(mut self, state: &M::State) -> std::io::Result<(Self, M::State)> {
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
        *jit.global(reg::N) = 5;
        let (mut jit, final_state) = jit.execute(&Start).expect("Execute failed");
        assert_eq!(final_state, Return);
        assert_eq!(*jit.global(reg::RESULT), 120);
    }
}
