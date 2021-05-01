use indexmap::{IndexSet};

use crate::util::{AsUsize};
use super::{code, optimizer};
use super::buffer::{Mmap};
use super::target::{x86_64};
use x86_64::{Label, Assembler, Lowerer, CALLEE_SAVES};
use code::{Action, TestOp, Machine, Precision, Slot, Value, IntoValue};
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
     * The number of pool slots used by the Convention. We allocate them
     * sequentially.
     */
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
    /** The test which must pass in order to execute `fetch`. */
    pub guard: (TestOp, Precision),
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

/**
 * The [`code::Register`] which conventionally holds the first function
 * argument.
 */
pub const ARG0: code::Register = unsafe {code::Register::new_unchecked(6)};

/**
 * The [`code::Register`] which conventionally holds the second function
 * argument.
 */
pub const ARG1: code::Register = unsafe {code::Register::new_unchecked(5)};

/**
 * The [`code::Register`] which conventionally holds the first return value.
 */
pub const RET0: code::Register = unsafe {code::Register::new_unchecked(0)};

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
            fetch_parent: fetch_parent,
            retire_parent: retire_parent,
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
pub struct JitInner {
    /** The code compiled so far. */
    lowerer: Lowerer<Mmap>,
    /** This nested struct can be borrowed independently of `lowerer`. */
    internals: Internals,
    /** The pool of mutable storage locations. */
    pool: Vec<u64>,
}

impl JitInner {
    pub fn new(code_size: usize, slots_used: usize) -> Self {
        let buffer = Mmap::new(code_size).expect("couldn't allocate memory");
        JitInner {
            lowerer: Lowerer {a: Assembler::new(buffer)},
            internals: Internals {
                specializations: Vec::new(),
                fetch_label: Label::new(None),
                retire_label: Label::new(None),
            },
            pool: vec![0; slots_used + 1 + 1000], // FIXME: replace "1000" by dynamically-calculated value.
        }._init()
    }

    fn _init(mut self) -> Self {
        let lo = &mut self.lowerer;
        // Assemble the function prologue and epilogue.
        if CALLEE_SAVES.len() & 1 != 1 {
            // Adjust alignment of RSP is 16-byte aligned.
            lo.a.push(CALLEE_SAVES[0]);
        }
        for &r in &CALLEE_SAVES {
            lo.a.push(r);
        }
        lo.a.move_(P64, x86_64::Register::R8, x86_64::Register::RDI);
        lo.a.const_jump(&mut self.internals.retire_label);
        // Root specializations are inserted here.
        lo.a.define(&mut self.internals.retire_label);
        lo.a.const_(P32, x86_64::Register::RA, -1);
        lo.a.define(&mut self.internals.fetch_label);
        for &r in CALLEE_SAVES.iter().rev() {
            lo.a.pop(r);
        }
        if CALLEE_SAVES.len() & 1 != 1 {
            // Adjust alignment of RSP is 16-byte aligned.
            lo.a.pop(CALLEE_SAVES[0]);
        }
        lo.a.ret();
        self
    }

    pub fn slot(&mut self, slot: impl IntoValue) -> &mut u64 {
        match slot.into() {
            Value::Register(_) => panic!("Not a Slot"),
            // TODO: Factor out pool index calculation.
            Value::Slot(Slot(index)) => &mut self.pool[index + 1],
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
        let mut fetch_label = Label::new(None);
        let mut retire_label = Label::new(None);
        let if_fail = self.internals.retire_label(fetch_parent);
        let here = lo.a.get_pos(); // Keep borrow-checker happy.
        *if_fail = if_fail.patch(&mut lo.a, here);
        lo.lower_test_op(guard, if_fail);
        for &action in fetch_code.iter() {
            lo.lower_action(action);
        }
        lo.a.define(&mut fetch_label);
        lo.a.const_jump(&mut retire_label);
        lo.a.define(&mut retire_label);
        // TODO: Optimize the case where `retire_code` is empty.
        // The preceding jump should jump straight to `retire_parent`.
        for &action in retire_code.iter() {
            lo.lower_action(action);
        }
        lo.a.const_jump(self.internals.fetch_label(retire_parent));
        let compiled = Compiled {
            guard, fetch_code, fetch_label, convention, retire_label, retire_code,
        };
        self.internals.new_specialization(fetch_parent, retire_parent, compiled)
    }

    /**
     * Compile code for a new [`Specialization`].
     *  - guard - the boolean test which distinguishes the new Specialization
     *    from its fetch parent. The new Specialization will be reached only if
     *    its fetch parent is reached and `test_op` passes.
     *  - actions - the code that must be executed before retiring to the
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
     * Call the compiled code, passing `&mut pool` and `argument`.
     * - bytes - the compiled code.
     */
    pub fn execute(mut self, argument: usize) -> std::io::Result<(Self, usize)> {
        // FIXME: assert we are on x86_64 at compile time.
        let pool = self.pool.as_mut_ptr();
        let (lowerer, ret) = self.lowerer.use_assembler(|a| {
            a.use_buffer(|b| {
                b.execute(|bytes| {
                    let f: RunFn = unsafe { std::mem::transmute(&bytes[0]) };
                    // Here is a good place to set a gdb breakpoint.
                    f(pool, argument)
                })
            })
        })?;
        self.lowerer = lowerer;
        Ok((self, ret))
    }
}

//-----------------------------------------------------------------------------

/** The state of the JIT compiler for a [`Machine`]. */
pub struct Jit<M: Machine> {
    /** The low-level bookkeeping data structures. */
    inner: JitInner,
    /** The [`Machine`]. */
    machine: M,
    /** The [`Convention`] used in the root states. */
    // TODO: One per state.
    convention: Convention,
    /** Numbering of all [`M::States`]. */
    states: IndexSet<M::State>,
    /** The [`Specialization`] corresponding to each [`M::State`]. */
    roots: Vec<Specialization>,
}

impl<M: Machine> Jit<M> {
    pub fn new(machine: M, code_size: usize) -> Self {
        // Construct the `JitInner`.
        let persistent_values = machine.values();
        let slots_used = persistent_values.iter().fold(0, |acc, &v| {
            match v {
                Value::Register(_r) => panic!("Persisting registers is not yet implemented"),
                Value::Slot(Slot(index)) => std::cmp::max(acc, index + 1),
            }
        });
        let inner = JitInner::new(code_size, slots_used);

        // Construct the Jit.
        let convention = Convention {live_values: persistent_values, slots_used: slots_used};
        let states = IndexSet::new();
        let roots = Vec::new();
        let mut jit = Jit {inner, machine, convention, states, roots};

        // Enumerate the reachable states in FIFO order and
        // construct the control-flow graph of the `Machine`.
        for state in jit.machine.initial_states() {
            jit.ensure_root(state);
        }
        let mut done = 0;
        while let Some(old_state) = jit.states.get_index(done).cloned() {
            let (_value_mask, cases) = jit.machine.get_code(old_state.clone());
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

    pub fn slot(&mut self, slot: impl IntoValue) -> &mut u64 {
        self.inner.slot(slot)
    }

    /** Ensure there is a root [`Specialization`] for `state`. */
    pub fn ensure_root(&mut self, state: M::State) {
        let index = self.roots.len();
        assert_eq!(index, self.states.len());
        if self.states.insert(state) {
            // Make a new root `Specialization`.
            self.roots.push(self.inner.compile_inner(
                None,
                None,
                (TestOp::Eq(ARG1.into(), index as i32), P32),
                Box::new([]),
                self.convention.clone(),
                Box::new([
                    Action::Constant(P32, RET0, index as i64),
                ]),
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
    use x86_64::{ALLOCATABLE_REGISTERS};

    /** An amount of code space suitable for running tests. */
    pub const CODE_SIZE: usize = 1 << 20;

    #[test]
    pub fn calling_regs() {
        // TODO: Move this and the values it tests somewhere more appropriate.
        assert_eq!(x86_64::Register::RDI, ALLOCATABLE_REGISTERS[ARG0.as_usize()]);
        assert_eq!(x86_64::Register::RSI, ALLOCATABLE_REGISTERS[ARG1.as_usize()]);
        assert_eq!(x86_64::Register::RA, ALLOCATABLE_REGISTERS[RET0.as_usize()]);
    }

    #[test]
    pub fn factorial() {
        use factorial::*;
        use State::*;

        let mut jit = Jit::new(Machine, CODE_SIZE);

        // Check the `states` list.
        let expected: IndexSet<_> = vec![
            Start, Loop, Return,
        ]
        .into_iter()
        .collect();
        assert_eq!(jit.states(), &expected);

        // Run some "code".
        *jit.slot(reg::N) = 5;
        let (mut jit, final_state) = jit.execute(&Start).expect("Execute failed");
        assert_eq!(final_state, Return);
        assert_eq!(*jit.slot(reg::RESULT), 120);
    }
}
