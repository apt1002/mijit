use super::code::*;
use Action::*;
use BinaryOp::*;
use Precision::*;

const R0: Register = REGISTERS[0];

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {Start, Loop}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Trap {Halt}

pub mod reg {
    use super::{Global, Variable};
    pub const N: Variable = Variable::Global(Global(0));
    pub const RESULT: Variable = Variable::Global(Global(1));
}

#[derive(Debug)]
pub struct Machine;

impl super::code::Machine for Machine {
    type State = State;
    type Trap = Trap;

    fn num_globals(&self) -> usize { 2 } // reg::N and reg::RESULT

    fn num_slots(&self) -> usize { 0 }

    fn liveness_mask(&self, _state: Self::State) -> u64 { 0 }

    fn prologue(&self) -> Vec<Action> { vec![] }

    fn epilogue(&self) -> Vec<Action> { vec![] }

    fn code(&self, state: Self::State) -> Switch<Case<Result<Self::State, Self::Trap>>> {
        match state {
            State::Start => Switch::always(
                Case {
                    actions: vec![
                        Constant(P32, R0, 1),
                        Move(reg::RESULT, R0.into()),
                    ],
                    new_state: Ok(State::Loop),
                },
            ),
            State::Loop => Switch::if_(
                reg::N,
                Case {
                    actions: vec![
                        Binary(Mul, P32, R0, reg::RESULT, reg::N),
                        Move(reg::RESULT, R0.into()),
                        Constant(P32, R0, 1),
                        Binary(Sub, P32, R0, reg::N, R0.into()),
                        Move(reg::N, R0.into()),
                    ],
                    new_state: Ok(State::Loop),
                },
                Case {
                    actions: vec![],
                    new_state: Err(Trap::Halt),
                },
            ),
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Start]
    }
}
