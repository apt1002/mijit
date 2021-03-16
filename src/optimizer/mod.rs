use std::collections::{HashMap};

use crate::util::{AsUsize};
use super::code::{self, Register, Action};
use super::jit::{Convention};
use super::jit::lowerer::{ALLOCATABLE_REGISTERS};

//-----------------------------------------------------------------------------

/** `ALLOCATABLE_REGISTERS.len()`. */
pub const NUM_REGISTERS: usize = ALLOCATABLE_REGISTERS.len();

/** An index into [`ALLOCATABLE_REGISTERS`]. */
// TODO: Move into `code`? See #23.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct RegIndex(usize);

/** Indicates an absent RegIndex. */
pub const DUMMY_REG: RegIndex = RegIndex(usize::MAX);

impl Default for RegIndex {
    fn default() -> Self { DUMMY_REG }
}

impl AsUsize for RegIndex {
    fn as_usize(self) -> usize {
        self.0
    }
}

/** Returns a fresh map from Register to RegIndex. */
// TODO: Delete. See #23.
pub fn map_from_register_to_index() -> HashMap<Register, RegIndex> {
    ALLOCATABLE_REGISTERS.iter()
        .enumerate()
        .map(|(i, &r)| (r, RegIndex(i)))
        .collect()
}

//-----------------------------------------------------------------------------

mod op;
pub use op::{Op};

mod dataflow;
pub use dataflow::{Dataflow, Node, DUMMY_NODE, Out, DUMMY_OUT};

mod simulation;
pub use simulation::{Simulation};

mod pool;
pub use pool::{RegisterPool};

mod pressure;
pub use pressure::{Pressure};

mod resources;
pub use resources::{Resources};

mod schedule;
pub use schedule::{Schedule};

mod codegen;
pub use codegen::{codegen};

/** Optimizes a basic block. */
pub fn optimize(
    _before: &Convention,
    actions: &[Action],
    _after: &Convention,
) -> Vec<Action> {
    // TODO.
    actions.iter().cloned().collect()
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::{HashMap};
    use super::*;
    use code::{Register, UnaryOp, BinaryOp, Precision};
    use code::tests::{Emulator};

    #[test]
    fn nop() {
        let before = Convention {
            live_values: vec![],
            slots_used: 0,
        };
        let actions = vec![];
        let after = Convention {
            live_values: vec![],
            slots_used: 0,
        };
        let observed = optimize(&before, &actions, &after);
        let expected: Vec<Action> = vec![];
        assert_eq!(observed.as_slice(), expected.as_slice());
    }

    #[test]
    fn one_ops() {
        const R0: Register = ALLOCATABLE_REGISTERS[0];
        const R1: Register = ALLOCATABLE_REGISTERS[1];
        let convention = Convention {
            live_values: vec![R0.into(), R1.into()],
            slots_used: 0,
        };
        let emulator = Emulator::new(convention.live_values.clone());
        use Precision::*;
        for action in &[
            Action::Constant(P64, R0, 924573497),
            Action::Unary(UnaryOp::Not, P64, R0, R1.into()),
            Action::Binary(BinaryOp::Add, P64, R0, R0.into(), R1.into()),
        ] {
            let actions = vec![action.clone()];
            let expected = emulator.execute(&actions);
            let optimized = optimize(&convention, &actions, &convention);
            let observed_with_temporaries = emulator.execute(&optimized);
            let observed: HashMap<_, _> = convention.live_values.iter().map(|&value| {
                let c = *observed_with_temporaries.get(&value).expect("Missing Value");
                (value, c)
            }).collect();
            if expected != observed {
                println!("actions = {:#?}", &actions);
                println!("optimized = {:#?}", &optimized);
                println!("expected = {:#?}", &expected);
                println!("observed = {:#?}", &observed);
                panic!("Optimized code does not do the same thing as the original");
            }
        }
    }
}
