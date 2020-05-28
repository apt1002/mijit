use super::control_flow::{Address, Action, Action::*, State, Machine};
//use super::code::{UnaryOp::*, BinaryOp::*, DivisionOp::*};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Variable;

/// Beetle's address space.
/// V is the type of a non-compile-time-known variable.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BeetleAddress {
    Ep,
    A,
    Sp,
    Rp,
    S0,
    R0,
    Throw,
    Bad,
    NotAddress,
    Memory(Variable), // TODO: work out what "Variable" really is.
}

use BeetleAddress::*;

impl Address for BeetleAddress {
    fn can_alias(&self, other: &Self) -> bool {
        match self {
            &Memory(_) => match other {
                &Memory(_) => true,
                _ => false,
            },
            _ => false,
        }
    }
}

pub fn machine() -> Machine<BeetleAddress> {
    const _CELL_BYTES: usize = 4;
    let _instructions: Vec<Vec<Action<BeetleAddress>>> = vec![
        vec![ // 00 NEXT
            Push(Ep),
        ],
    ];
    // Construct the decoder tree.
    let states: Vec<State<BeetleAddress>> = vec![];

    // Return the machine.
    Machine {states}
}