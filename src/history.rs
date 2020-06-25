use indexmap::IndexSet;

use super::{code, control_flow};
use control_flow::{Machine};

pub struct CallingConvention;

pub struct History<A: control_flow::Address> {
    pub test: code::TestOp,
    pub fetch: Vec<code::Action<A>>,
    pub calling_convention: CallingConvention,
    pub register: code::R,
    pub retire: Vec<code::Action<A>>,
}

pub struct Jit<M: Machine> {
    states: IndexSet<M::State>,
}

impl<M: Machine> Jit<M> {
    pub fn new(machine: M) -> Self {
        let mut states: IndexSet<_> = machine.initial_states().into_iter().collect();
        let mut done = 0;
        while let Some(state) = states.get_index(done) {
            for (_test_op, _actions, new_state) in machine.get_code(state.clone()) {
                let (_, _) = states.insert_full(new_state);
            }
            done += 1;
        }
        Jit {states}
    }

    pub fn states(&self) -> &IndexSet<M::State> {
        &self.states
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    pub fn beetle() {
        use super::super::{beetle};
        use beetle::State::*;
        let jit = Jit::new(beetle::Machine);
        let expected: IndexSet<_> = vec![
            Root, Dispatch, Next, Pick, Roll, Qdup, Abs, Max, Min, Lshift,
            Rshift, Branch, Branchi, Qbranch, Qbranchi, Loop, Loopi, Ploop,
            Ploopi, Ploopp, Ploopm, Ploopip, Ploopim,
        ].into_iter().collect();
        assert_eq!(jit.states(), &expected);
    }
}
