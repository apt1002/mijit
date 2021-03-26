use super::code::*;
use Action::*;
use BinaryOp::*;
use Precision::*;
use Register::{RA};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {Start, Loop, Return}

pub mod reg {
    use super::{Slot, Value};
    pub const N: Value = Value::Slot(Slot(0));
    pub const RESULT: Value = Value::Slot(Slot(1));
}

#[derive(Debug)]
pub struct Machine;

impl super::code::Machine for Machine {
    type State = State;

    fn num_globals(&self) -> usize { 2 }
    
    fn get_code(&self, state: Self::State) ->
        Vec<(
            (TestOp, Precision),
            Vec<Action>,
            Self::State,
        )>
    {
        match state {
            State::Start => {vec![
                ((TestOp::Always, P32), vec![
                    Constant(P32, RA, 1),
                    Move(reg::RESULT, RA.into()),
                ], State::Loop),
            ]},
            State::Loop => {vec![
                ((TestOp::Eq(reg::N, 0), P32), vec![
                ], State::Return),
                ((TestOp::Ne(reg::N, 0), P32), vec![
                    Binary(Mul, P32, RA, reg::RESULT, reg::N),
                    Move(reg::RESULT, RA.into()),
                    Constant(P32, RA.into(), 1),
                    Binary(Sub, P32, RA, reg::N, RA.into()),
                    Move(reg::N, RA.into()),
                ], State::Loop),
            ]},
            State::Return => {vec![]},
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Start]
    }
}
