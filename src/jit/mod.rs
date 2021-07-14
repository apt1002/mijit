use indexmap::{IndexSet};

use super::{code, target, optimizer};
use super::target::{Word, Target, STATE_INDEX};
use code::{Action, TestOp, Machine, Precision, Global, Variable, FAST_VALUES};
use Precision::*;

mod engine;
use engine::{Engine, Specialization};

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
    /** The [`Variable`] that will be tested next. */
    // pub discriminant: Variable,
    /** The values that are live on entry, including `discriminant`. */
    pub live_values: Vec<Variable>,
    /**
     * The number of spill [`Slot`]s used by the Convention.
     *
     * [`Slot`]: code::Slot
     */
    pub slots_used: usize,
}

//-----------------------------------------------------------------------------

/** The state of the JIT compiler for a [`Machine`]. */
pub struct Jit<M: Machine, T: Target> {
    /** The low-level bookkeeping data structures. */
    engine: Engine<T>,
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
        // Construct the `Engine`.
        let engine = Engine::new(target, machine.num_globals());

        // Construct the Jit.
        let states = IndexSet::new();
        let roots = Vec::new();
        let mut jit = Jit {engine, machine, states, roots};

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
        self.engine.global_mut(global)
    }

    /** Ensure there is a root [`Specialization`] for `state`. */
    pub fn ensure_root(&mut self, state: M::State) {
        let index = self.roots.len();
        assert_eq!(index, self.states.len());
        if self.states.insert(state.clone()) {
            // Make a new root `Specialization`.
            let mask = self.machine.liveness_mask(state);
            let live_values: Vec<Variable> = (0..FAST_VALUES.len())
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
            self.roots.push(self.engine.compile_inner(
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
        self.engine.compile(
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
        let (engine, new_index) = self.engine.execute(index)?;
        let new_index = new_index.u as usize;
        self.engine = engine;
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

    use engine::{Statistics};
    use target::{Word, native};

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
        let observed = jit.engine.compute_statistics();
        for (s, expected) in jit.engine.all_specializations().zip(&expected) {
            assert_eq!(expected, &observed[s]);
        }
    }
}
