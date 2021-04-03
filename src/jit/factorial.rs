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
    
    fn get_code(&self, state: Self::State) -> (u64, Vec<Case<Self::State>>) {
        match state {
            State::Start => (
                0x1, // N
                vec![
                    Case {
                        condition: (TestOp::Always, P32),
                        actions: vec![
                            Constant(P32, R0, 1),
                            Move(reg::RESULT, R0.into()),
                        ],
                        new_state: State::Loop,
                    },
                ],
            ),
            State::Loop => (
                0x3, // N, RESULT
                vec![
                    Case {
                        condition: (TestOp::Eq(reg::N, 0), P32),
                        actions: vec![],
                        new_state: State::Return,
                    },
                    Case {
                        condition: (TestOp::Ne(reg::N, 0), P32),
                        actions: vec![
                            Binary(Mul, P32, R0, reg::RESULT, reg::N),
                            Move(reg::RESULT, R0.into()),
                            Constant(P32, R0.into(), 1),
                            Binary(Sub, P32, R0, reg::N, R0.into()),
                            Move(reg::N, R0.into()),
                        ],
                        new_state: State::Loop,
                    },
                ],
            ),
            State::Return => (
                0x2, // RESULT
                vec![],
            ),
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Start]
    }
}
