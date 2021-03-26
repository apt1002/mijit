use std::collections::{HashMap};
use std::fmt::{self, Debug, Formatter};

use crate::util::{AsUsize};
use super::code::{self, Register, Action};
use super::jit::{Convention};
use super::jit::lowerer::{ALLOCATABLE_REGISTERS};

//-----------------------------------------------------------------------------

/** `ALLOCATABLE_REGISTERS.len()`. */
pub const NUM_REGISTERS: usize = ALLOCATABLE_REGISTERS.len();

/** An index into [`ALLOCATABLE_REGISTERS`]. */
// TODO: Move into `code`? See #23.
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub struct RegIndex(usize);

impl Debug for RegIndex {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "RI{}", self.0)
    }
}

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

mod resources;
pub use resources::{Resources};

mod cost;
pub use cost::{BUDGET, SPILL_COST, SLOT_COST, Cost, op_cost};

mod dataflow;
pub use dataflow::{Dataflow, Node, DUMMY_NODE, Out, DUMMY_OUT};

mod simulation;
pub use simulation::{Simulation};

mod pool;
pub use pool::{RegisterPool};

mod pressure;
pub use pressure::{Pressure}; // Unused so far.

mod placer;
pub use placer::{Placer};

mod schedule;
pub use schedule::{Schedule};

mod moves;
pub use moves::{moves};

mod codegen;
pub use codegen::{codegen};

/** Optimizes a basic block. */
pub fn optimize(before: &Convention, after: &Convention, actions: &[Action]) -> Vec<Action> {
    let mut simulation = Simulation::new(&before.live_values);
    for action in actions {
        simulation.action(action);
    }
    let (dataflow, exit_node) = simulation.finish(&after.live_values);
    let nodes: Vec<_> = dataflow.all_nodes().collect(); // TODO.
    assert_eq!(dataflow.entry_node(), nodes[0]);
    assert_eq!(exit_node, nodes[nodes.len()-1]);
    let nodes = &nodes[1..nodes.len()-1];
    let schedule = Schedule::new(&dataflow, nodes, exit_node);
    codegen(before, after, schedule, exit_node)
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::{HashMap};
    use super::*;
    use code::{Register, Slot, UnaryOp, BinaryOp, AliasMask, Precision, Width};
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
        let observed = optimize(&before, &after, &actions);
        let expected: Vec<Action> = vec![];
        assert_eq!(observed.as_slice(), expected.as_slice());
    }

    #[test]
    fn one_ops() {
        const V0: Register = ALLOCATABLE_REGISTERS[0];
        const V1: Slot = Slot(0);
        let convention = Convention {
            live_values: vec![V0.into(), V1.into()],
            slots_used: 1,
        };
        let emulator = Emulator::new(convention.live_values.clone());
        use Precision::*;
        for action in &[
            Action::Constant(P64, V0, 924573497),
            Action::Unary(UnaryOp::Not, P64, V0, V1.into()),
            Action::Binary(BinaryOp::Add, P64, V0, V0.into(), V1.into()),
        ] {
            let actions = vec![action.clone()];
            let expected = emulator.execute(&actions);
            let optimized = optimize(&convention, &convention, &actions);
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

    #[test]
    fn use_after_free() {
        use Precision::*;
        use Width::*;
        const V0: Register = ALLOCATABLE_REGISTERS[0];
        const V1: Register = ALLOCATABLE_REGISTERS[1];
        let before = Convention {
            live_values: vec![V0.into(), V1.into()],
            slots_used: 1,
        };
        let actions = vec![
            Action::Store(V1.into(), (V0, Four), AliasMask(1)),
            Action::Constant(P64, V0, 1234),
        ];
        let after = Convention {
            live_values: vec![V0.into()],
            slots_used: 1,
        };
        let _ = optimize(&before, &after, &actions);
        // Just don't panic!
    }
}
