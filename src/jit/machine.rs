use std::collections::{HashMap};
use indexmap::{IndexSet};

use super::{code, target, engine};
use code::{Case, Switch, Machine, REGISTERS, Global, Slot, Variable, Convention};
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
        let slots_used = machine.num_slots();
        let mut live_values = Vec::new();
        live_values.extend(REGISTERS.iter().map(|&r| Variable::from(r)));
        live_values.extend((0..slots_used).map(|s| Variable::from(Slot(s))));
        live_values.extend((0..num_globals).map(|g| Variable::from(Global(g))));
        let mut engine = Engine::new(
            target,
            num_globals,
            Convention {live_values, slots_used},
            machine.prologue().into(),
            machine.epilogue().into(),
        );

        // Flood fill to find all reachable `M::State`s.
        // Make an `EntryId` for each `Case`.
        let mut state_index = IndexSet::new();
        let mut trap_index = IndexSet::new();
        let mut switches: Vec<Switch<(Case<Result<M::State, M::Trap>>, EntryId)>> = Vec::new();
        state_index.extend(machine.initial_states());
        while let Some(old_state) = state_index.get_index(switches.len()) {
            switches.push(machine.code(old_state.clone()).map(|case| {
                match &case.new_state {
                    Ok(state) => state_index.insert(state.clone()),
                    Err(trap) => trap_index.insert(trap.clone()),
                };
                (case.clone(), engine.new_entry(NOT_IMPLEMENTED))
            }));
        }

        // Make and define an `EntryId` for each `Switch`.
        // Also, make a `Switch<EntryId>` for each `Switch`.
        let state_infos: Vec<_> = switches.iter().map(|switch| {
            let entry = engine.new_entry(NOT_IMPLEMENTED);
            let switch = switch.map(|&(_, case_entry)| case_entry);
            engine.define(
                entry,
                Box::new([]), /* prologue */
                &switch,
            );
            (entry, switch)
        }).collect();

        // Make and define an `EntryId` for each `Trap`.
        // Also, make a `Switch<EntryId>` for each `Trao`.
        let trap_infos: Vec<_> = (0..trap_index.len() as i64).map(|exit_value| {
            assert!(exit_value < NOT_IMPLEMENTED);
            let entry = engine.new_entry(exit_value);
            Switch::Always(entry)
        }).collect();

        // Fill in the code for states.
        let states = state_index.iter().enumerate().map(|(i, state)| {
            let _ = switches[i].map(|&(ref case, case_entry)| {
                match &case.new_state {
                    Ok(new_state) => {
                        engine.define(
                            case_entry,
                            case.actions.clone().into(),
                            &state_infos[state_index.get_index_of(new_state).unwrap()].1,
                        );
                    },
                    Err(trap) => {
                        engine.define(
                            case_entry,
                            case.actions.clone().into(),
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
