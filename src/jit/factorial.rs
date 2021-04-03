use super::code::*;
use Action::*;
use BinaryOp::*;
use Precision::*;

const R0: Register = REGISTERS[0];

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

    fn values(&self) -> Vec<Value> {
        vec![reg::N, reg::RESULT]
    }
    
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
                    Constant(P32, R0, 1),
                    Move(reg::RESULT, R0.into()),
                ], State::Loop),
            ]},
            State::Loop => {vec![
                ((TestOp::Eq(reg::N, 0), P32), vec![
                ], State::Return),
                ((TestOp::Ne(reg::N, 0), P32), vec![
                    Binary(Mul, P32, R0, reg::RESULT, reg::N),
                    Move(reg::RESULT, R0.into()),
                    Constant(P32, R0.into(), 1),
                    Binary(Sub, P32, R0, reg::N, R0.into()),
                    Move(reg::N, R0.into()),
                ], State::Loop),
            ]},
            State::Return => {vec![]},
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Start]
    }
}
