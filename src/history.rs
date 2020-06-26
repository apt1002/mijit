use std::{mem};

use indexmap::IndexSet;

use super::{Assembler, Buffer, code, control_flow, x86_64};
use control_flow::{Machine};
use x86_64::*;
use Register::*;
use BinaryOp::*;
use Condition;

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
    buffer: Buffer,
}

impl<M: Machine> Jit<M> {
    pub fn new(machine: M, code_size: usize) -> Self {
        let mut states: IndexSet<_> = machine.initial_states().into_iter().collect();
        let mut buffer = Buffer::new(code_size).expect("couldn't allocate memory");
        let mut a = Assembler::new(&mut buffer);
        let mut done = 0;
        while let Some(state) = states.get_index(done) {
            let index = done;
            a.const_op(Cmp, R8, done as i32);
            let patch = a.jump_if(Condition::Z, true, None);
            for (_test_op, _actions, new_state) in machine.get_code(state.clone()) {
                let (_, _) = states.insert_full(new_state);
            }
            done += 1;
        }
        Jit {states, buffer}
    }

    pub fn states(&self) -> &IndexSet<M::State> {
        &self.states
    }

    pub fn execute(mut self, state: M::State) -> (Self, M::State) {
        let index = self.states.get_index_of(&state).expect("invalid state");
        let (buffer, new_index) = self.buffer.execute(|bytes| {
            // FIXME: assert we are on x86_64 at compile time.
            let f: extern "C" fn(usize) -> usize = unsafe {mem::transmute(&bytes[0])};
            f(index)
        }).expect("Couldn't change permissions");
        self.buffer = buffer;
        let new_state = self.states.get_index(new_index).expect("invalid index").clone();
        (self, new_state)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    const CODE_SIZE: usize = 1 << 20;

    #[test]
    pub fn beetle() {
        use super::super::{beetle};
        use beetle::State::*;
        let jit = Jit::new(beetle::Machine, CODE_SIZE);
        let expected: IndexSet<_> = vec![
            Root, Dispatch, Next, Pick, Roll, Qdup, Abs, Max, Min, Lshift,
            Rshift, Branch, Branchi, Qbranch, Qbranchi, Loop, Loopi, Ploop,
            Ploopi, Ploopp, Ploopm, Ploopip, Ploopim,
        ].into_iter().collect();
        assert_eq!(jit.states(), &expected);
    }
}
