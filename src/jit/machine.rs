use std::collections::{HashMap};
use indexmap::{IndexSet};

use super::{code, target, engine};
use code::{Case, Switch, Machine, Global, Variable, FAST_VARIABLES, Convention};
use target::{Word, Target};
use engine::{Engine, EntryId};

/** Exit value for incomplete compilation. */
pub const NOT_IMPLEMENTED: i64 = i64::MAX;

/** The state of the JIT compiler for a [`Machine`]. */
pub struct Jit<M: Machine, T: Target> {
    /** The low-level bookkeeping data structures. */
    engine: Engine<T>,
    /** Maps `Machine::State`s to the corresponding `EntryId`s. */
    states: HashMap<M::State, EntryId>,
    /** Maps `Machine::Trap`s to the corresponding exit values. */
    trap_index: IndexSet<M::Trap>,
}

impl<M: Machine, T: Target> Jit<M, T> {
    pub fn new(machine: M, target: T) -> Self {
        // Construct the `Engine`.
        let num_globals = machine.num_globals();
        let mut engine = Engine::new(target, num_globals);

        // Used by `Entry`s for `Case`s.
        let prologue = machine.prologue().into_boxed_slice();
        let epilogue = machine.epilogue().into_boxed_slice();

        // Used by `Entry`s for `Switch`es and `Trap`s.
        let empty_convention = Convention {
            slots_used: machine.num_slots(),
            live_values: (0..num_globals).map(|g| Variable::from(Global(g))).collect(),
        };

        // Flood fill to find all reachable `M::State`s.
        // Make an `EntryId` for each `Case`.
        let mut state_index = IndexSet::new();
        let mut trap_index = IndexSet::new();
        struct CaseAndEntry<M: Machine> {
            case: Case<Result<M::State, M::Trap>>,
            entry: EntryId,
        }
        let mut switches: Vec<Switch<CaseAndEntry<M>>> = Vec::new();
        state_index.extend(machine.initial_states());
        while let Some(old_state) = state_index.get_index(switches.len()) {
            let liveness_mask = machine.liveness_mask(old_state.clone());
            let convention = Convention {
                slots_used: machine.num_slots(),
                live_values: (0..FAST_VARIABLES.len())
                    .filter(|i| liveness_mask & (1 << i) != 0)
                    .map(|i| FAST_VARIABLES[i])
                    .chain((0..num_globals).map(|g| Variable::from(Global(g))))
                    .collect(),
            };
            let switch = machine.code(old_state.clone()).map(|case| {
                match &case.new_state {
                    Ok(state) => state_index.insert(state.clone()),
                    Err(trap) => trap_index.insert(trap.clone()),
                };
                let entry = engine.new_entry(
                    prologue.clone(),
                    convention.clone(),
                    // TODO: Set dead [`Variable`]s to `0xdeaddeaddeaddead`.
                    // We get away with this because we don't optimize epilogues.
                    epilogue.clone(),
                    NOT_IMPLEMENTED,
                );
                CaseAndEntry {case: case.clone(), entry: entry}
            });
            switches.push(switch);
        }

        // Make and define an `EntryId` for each `Switch`.
        // Also, make a `Switch<EntryId>` for each `Switch`.
        let state_infos: Vec<_> = switches.iter().map(|switch| {
            let entry = engine.new_entry(
                Box::new([]),
                empty_convention.clone(),
                Box::new([]),
                NOT_IMPLEMENTED,
            );
            let switch = switch.map(|ce| ce.entry);
            engine.define(
                entry,
                prologue.clone(),
                &switch,
            );
            (entry, switch)
        }).collect();

        // Make and define an `EntryId` for each `Trap`.
        // Also, make a `Switch<EntryId>` for each `Trap`.
        let trap_infos: Vec<_> = (0..trap_index.len() as i64).map(|exit_value| {
            assert!(exit_value < NOT_IMPLEMENTED);
            let entry = engine.new_entry(
                Box::new([]),
                empty_convention.clone(),
                Box::new([]),
                exit_value,
            );
            Switch::Always(entry)
        }).collect();

        // Fill in the code for states.
        let states = state_index.iter().enumerate().map(|(i, state)| {
            let _ = switches[i].map(|ce| {
                match &ce.case.new_state {
                    Ok(new_state) => {
                        engine.define(
                            ce.entry,
                            ce.case.actions.clone().into(),
                            &state_infos[state_index.get_index_of(new_state).unwrap()].1,
                        );
                    },
                    Err(trap) => {
                        // TODO: Set dead [`Variable`]s to `0xdeaddeaddeaddead`.
                        // We get away with this because we don't optimize epilogues.
                        let actions: Vec<_> = ce.case.actions.iter().chain(epilogue.iter()).copied().collect();
                        engine.define(
                            ce.entry,
                            actions.into(),
                            &trap_infos[trap_index.get_index_of(trap).unwrap()],
                        );
                    },
                }
            });
            (state.clone(), state_infos[i].0)
        }).collect();

        Jit {engine, states, trap_index}
    }

    pub fn global_mut(&mut self, global: Global) -> &mut Word {
        self.engine.global_mut(global)
    }

    /**
     * Call the compiled code, starting in `state`.
     *
     * # Safety
     *
     * This will crash if the code is compiled for the wrong [`Target`] or if
     * the code returned by the [`Machine`] is invalid.
     */
    pub unsafe fn execute(mut self, state: &M::State) -> std::io::Result<(Self, M::Trap)> {
        let entry = *self.states.get(state).expect("invalid state");
        let (engine, exit_value) = self.engine.run(entry)?;
        let trap = self.trap_index.get_index(exit_value.s as usize).unwrap().clone();
        self.engine = engine;
        Ok((self, trap))
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    use std::convert::{TryFrom};

    use target::{Word, native};

    #[test]
    pub fn factorial() {
        use super::super::factorial::*;
        use State::*;
        use Trap::*;

        let mut jit = Jit::new(Machine, native());

        // Check the `states` list.
        assert_eq!(jit.states.len(), 2); // Start, Loop.

        // Run some "code".
        *jit.global_mut(Global::try_from(reg::N).unwrap()) = Word {u: 5};
        let (mut jit, trap) = unsafe {
            jit.execute(&Start).expect("Execute failed")
        };
        assert_eq!(trap, Halt);
        assert_eq!(*jit.global_mut(Global::try_from(reg::RESULT).unwrap()), Word {u: 120});
    }
}
