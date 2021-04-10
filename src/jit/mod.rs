use indexmap::{IndexSet};

use crate::util::{AsUsize};
use super::{Buffer, code, optimizer, x86_64};
use x86_64::{Label, Assembler, CALLEE_SAVES};
use code::{Action, TestOp, Machine, Precision, Slot, Value, IntoValue};
use Precision::*;

pub mod lowerer;
use lowerer::{Lowerer, ALLOCATABLE_REGISTERS};

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
    /** The fetch parent, or `None` if this is the least specialization. */
    pub fetch_parent: Option<Specialization>,
    /** The retire parent, or `None` if this is the least specialization. */
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
    /** The address just after `fetch`. Retire children jump here. */
    pub fetch_label: Label,
    /** The interface from `fetch` to `retire`. Obeyed by children. */
    pub convention: Convention,
    /** The address just before `retire`. The last fetch child jumps here. */
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

//-----------------------------------------------------------------------------

/**
 * The state of the JIT compiler. This includes the memory allocated for the
 * compiled code, and all house-keeping data.
 */
#[allow(clippy::module_name_repetitions)]
pub struct JitInner {
    /**
     * The specializations in the order they were compiled, including the
     * least specialization. Indexed by [`Specialization`].
     */
    specializations: Vec<(Relatives, Compiled)>,
    /** The pool of mutable storage locations. */
    pool: Vec<u64>,
}

impl JitInner {
    pub fn new(lo: &mut Lowerer, slots_used: usize) -> Self {
        let specializations = Vec::new();
        // TODO: Factor out pool index calculation.
        let pool = vec![0; slots_used + 1 + 1000]; // FIXME: replace "1000" by dynamically-calculated value.
        let mut this = JitInner {specializations, pool};

        // Assemble the function prologue and epilogue.
        let mut fetch_label = Label::new(None);
        let mut retire_label = Label::new(None);
        if CALLEE_SAVES.len() & 1 != 1 {
            // Adjust alignment of RSP is 16-byte aligned.
            lo.a.push(CALLEE_SAVES[0]);
        }
        for &r in &CALLEE_SAVES {
            lo.a.push(r);
        }
        lo.a.move_(P64, x86_64::Register::R8, x86_64::Register::RDI);
        lo.a.const_(P32, x86_64::Register::RA, -1);
        lo.a.const_jump(&mut retire_label);
        // Root specializations are inserted here.
        lo.a.define(&mut retire_label);
        lo.a.define(&mut fetch_label);
        for &r in CALLEE_SAVES.iter().rev() {
            lo.a.pop(r);
        }
        if CALLEE_SAVES.len() & 1 != 1 {
            // Adjust alignment of RSP is 16-byte aligned.
            lo.a.pop(CALLEE_SAVES[0]);
        }
        lo.a.ret();

        // Only `fetch_label` and `retire_label` matter.
        let compiled = Compiled {
            guard: (TestOp::Always, P64),
            fetch_code: Box::new([]),
            fetch_label: fetch_label,
            convention: Convention {live_values: Vec::new(), slots_used},
            retire_label: retire_label,
            retire_code: Box::new([]),
        };
        this.new_specialization(None, None, compiled);
        this
    }

    pub fn slot(&mut self, slot: impl IntoValue) -> &mut u64 {
        match slot.into() {
            Value::Register(_) => panic!("Not a Slot"),
            // TODO: Factor out pool index calculation.
            Value::Slot(Slot(index)) => &mut self.pool[index + 1],
        }
    }

    /** Returns the least [`Specialization`]. */
    pub const fn least_specialization(&self) -> Specialization {
        unsafe { Specialization::new_unchecked(0) }
    }

    /** Returns the [`Relatives`] of a [`Specialization`]. */
    fn relatives(&mut self, s: Specialization) -> &mut Relatives {
        &mut self.specializations[s.as_usize()].0
    }

    /** Returns the [`Compiled`] of a [`Specialization`]. */
    fn compiled(&mut self, s: Specialization) -> &mut Compiled {
        &mut self.specializations[s.as_usize()].1
    }

    /** Constructs a new specialization and informs its relatives. */
    fn new_specialization(
        &mut self,
        fetch_parent: Option<Specialization>,
        retire_parent: Option<Specialization>,
        compiled: Compiled,
    ) -> Specialization {
        let this = Specialization::new(self.specializations.len()).unwrap();
        if let Some(parent) = fetch_parent {
            self.relatives(parent).fetch_children.push(this);
        }
        if let Some(parent) = retire_parent {
            self.relatives(parent).retire_children.push(this);
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

    /**
     * Compile code for a new [`Specialization`].
     * Unlike `compile()`, this method does not do any optimization. The caller
     * has control over `fetch_code`, `convention` and `retire_code`.
     */
    pub fn compile_inner(
        &mut self,
        lo: &mut Lowerer,
        fetch_parent: Specialization,
        retire_parent: Specialization,
        guard: (TestOp, Precision),
        fetch_code: Box<[Action]>,
        convention: Convention,
        retire_code: Box<[Action]>,
    ) -> Specialization {
        let mut fetch_label = Label::new(None);
        let mut retire_label = Label::new(None);
        let here = lo.a.get_pos(); // Keep borrow-checker happy.
        let if_fail = &mut self.compiled(fetch_parent).retire_label;
        *if_fail = if_fail.patch(&mut lo.a, here);
        let (test_op, prec) = guard;
        lo.lower_test_op(test_op, prec, if_fail);
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
        lo.a.const_jump(&mut self.compiled(retire_parent).fetch_label);
        let compiled = Compiled {
            guard, fetch_code, fetch_label, convention, retire_label, retire_code,
        };
        self.new_specialization(Some(fetch_parent), Some(retire_parent), compiled)
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
        lo: &mut Lowerer,
        fetch_parent: Specialization,
        retire_parent: Specialization,
        guard: (TestOp, Precision),
        actions: &[Action],
    ) -> Specialization {
        let fetch_convention = self.compiled(fetch_parent).convention.clone();
        let retire_convention = self.compiled(retire_parent).convention.clone();
        let fetch_code = optimizer::optimize(
            &fetch_convention,
            &retire_convention,
           actions,
        );
        let convention = self.compiled(retire_parent).convention.clone();
        self.compile_inner(
            lo,
            fetch_parent,
            retire_parent,
            guard,
            fetch_code,
            convention,
            Box::new([]),
        )
    }

    /**
     * Call the compiled code, passing `&mut pool` and `argument`.
     * - bytes - the compiled code.
     */
    pub fn execute(&mut self, bytes: &[u8], argument: usize) -> usize {
        // FIXME: assert we are on x86_64 at compile time.
        let f: RunFn = unsafe { std::mem::transmute(&bytes[0]) };
        let pool = self.pool.as_mut_ptr();
        // Here is a good place to set a gdb breakpoint.
        f(pool, argument)
    }
}

//-----------------------------------------------------------------------------

/** The state of the JIT compiler for a [`Machine`]. */
pub struct Jit<M: Machine> {
    /** The low-level bookkeeping data structures. */
    inner: JitInner,
    /** The [`Machine`]. */
    machine: M,
    /** The mmapped memory buffer containing the compiled code. */
    buffer: Buffer,
    /** The number of bytes of `buffer` already occupied. */
    used: usize,
    /** Numbering of all [`M::States`]. */
    states: IndexSet<M::State>,
    /** The [`Specialization`] corresponding to each [`M::State`]. */
    roots: Vec<Specialization>,
}

impl<M: Machine> Jit<M> {
    pub fn new(machine: M, code_size: usize) -> Self {
        let mut buffer = Buffer::new(code_size).expect("couldn't allocate memory");

        // Construct the `JitInner`.
        let mut lo = Lowerer {a: Assembler::new(&mut buffer)};
        let persistent_values = machine.values();
        let slots_used = persistent_values.iter().fold(0, |acc, &v| {
            match v {
                Value::Register(_r) => panic!("Persisting registers is not yet implemented"),
                Value::Slot(Slot(index)) => std::cmp::max(acc, index + 1),
            }
        });
        let mut inner = JitInner::new(&mut lo, slots_used);

        // Enumerate the reachable states in FIFO order.
        let mut states: IndexSet<M::State> = machine.initial_states().into_iter().collect();
        let mut done = 0;
        while let Some(state) = states.get_index(done) {
            for case in machine.get_code(state.clone()).1 {
                states.insert(case.new_state);
            }
            done += 1;
        }

        // Construct the root Specializations.
        let reg_arg0 = unsafe {code::Register::new_unchecked(6)};
        let reg_arg1 = unsafe {code::Register::new_unchecked(5)};
        let reg_ret = unsafe {code::Register::new_unchecked(0)};
        assert_eq!(x86_64::Register::RDI, ALLOCATABLE_REGISTERS[reg_arg0.as_usize()]);
        assert_eq!(x86_64::Register::RSI, ALLOCATABLE_REGISTERS[reg_arg1.as_usize()]);
        assert_eq!(x86_64::Register::RA, ALLOCATABLE_REGISTERS[reg_ret.as_usize()]);
        let mut roots = Vec::new();
        for (index, _state) in states.iter().enumerate() {
            let specialization = inner.compile_inner(
                &mut lo,
                inner.least_specialization(),
                inner.least_specialization(),
                (TestOp::Eq(reg_arg1.into(), index as i32), P32),
                Box::new([]),
                Convention {
                    live_values: persistent_values.clone(), // TODO: Refine.
                    slots_used: slots_used,
                },
                Box::new([
                    Action::Constant(P32, reg_ret, index as i64),
                ]),
            );
            roots.push(specialization);
        }

        // Construct the Jit.
        let used = lo.a.get_pos();
        let mut jit = Jit {inner, machine, buffer, used, states, roots};

        // Construct the root Histories.
        let all_states: Vec<_> = jit.states.iter().cloned().collect();
        for old_state in all_states {
            let (_value_mask, cases) = jit.machine.get_code(old_state.clone());
            for case in cases {
                jit.compile(old_state.clone(), case.condition, &case.actions, case.new_state);
            }
        }

        jit
    }

    pub fn used(&self) -> usize {
        self.used
    }

    pub fn states(&self) -> &IndexSet<M::State> {
        &self.states
    }

    pub fn slot(&mut self, slot: impl IntoValue) -> &mut u64 {
        self.inner.slot(slot)
    }

    pub fn compile(
        &mut self,
        old_state: M::State,
        guard: (TestOp, Precision),
        actions: &[Action],
        new_state: M::State,
    ) -> Specialization {
        let mut lo = Lowerer {a: Assembler::new(&mut self.buffer)};
        lo.a.set_pos(self.used);
        let ret = self.inner.compile(
            &mut lo,
            self.roots[self.states.get_index_of(&old_state).unwrap()],
            self.roots[self.states.get_index_of(&new_state).unwrap()],
            guard,
            actions,
        );
        self.used = lo.a.get_pos();
        ret
    }

    pub fn execute(mut self, state: M::State) -> (Self, M::State) {
        let index = self.states.get_index_of(&state).expect("invalid state");
        let inner = &mut self.inner;
        let (buffer, new_index) = self.buffer.execute(|bytes| {
            inner.execute(bytes, index)
        }).expect("Couldn't change permissions");
        self.buffer = buffer;
        let new_state = self.states.get_index(new_index).expect("invalid index").clone();
        (self, new_state)
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod factorial;

#[cfg(test)]
pub mod tests {
    use super::*;

    /** An amount of code space suitable for running tests. */
    pub const CODE_SIZE: usize = 1 << 20;

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
        let (mut jit, final_state) = jit.execute(Start);
        assert_eq!(final_state, Return);
        assert_eq!(*jit.slot(reg::RESULT), 120);
    }
}
