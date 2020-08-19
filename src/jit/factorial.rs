use super::code::*;
use Action::*;
use BinaryOp::*;
use Precision::*;
use R::*;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum State {Start, Loop, Return}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Global {N, Result}

impl super::code::Alias for () {}

#[derive(Debug)]
pub struct Machine;

impl super::code::Machine for Machine {
    type State = State;
    type Global = Global;
    type Memory = ();
    
    fn get_code(&self, state: Self::State) ->
        Vec<(
            (TestOp, Precision),
            Vec<Action<Self::Memory, Self::Global>>,
            Self::State,
        )>
    {
        match state {
            State::Start => {vec![
                ((TestOp::Always, P32), vec![
                    Constant(P32, RD, 1),
                    LoadGlobal(RA, Global::N),
                ], State::Loop),
            ]},
            State::Loop => {vec![
                ((TestOp::Eq(RA, 0), P32), vec![
                    StoreGlobal(RD, Global::Result),
                ], State::Return),
                ((TestOp::Ne(RA, 0), P32), vec![
                    Binary(Mul, P32, RD, RD, RA),
                    Constant(P32, RC, 1),
                    Binary(Sub, P32, RA, RA, RC),
                ], State::Loop),
            ]},
            State::Return => {vec![]},
        }
    }

    fn initial_states(&self) -> Vec<Self::State> {
        vec![State::Start]
    }
}
