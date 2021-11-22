use super::code::{self, Register};

const NUM_REGISTERS: usize = super::target::x86_64::ALLOCATABLE_REGISTERS.len();

fn all_registers() -> impl Iterator<Item=Register> {
    (0..NUM_REGISTERS).map(|i| Register::new(i as u8).unwrap())
}

//-----------------------------------------------------------------------------

mod ebb;
pub use ebb::{Leaf, EBB};

mod op;
pub use op::{Op};

mod resources;
pub use resources::{Resources};

mod cost;
pub use cost::{BUDGET, SPILL_COST, SLOT_COST, Cost, op_cost};

mod dataflow;
pub use dataflow::{Dataflow, Node, Out};

mod cft;
pub use cft::{Switch, Cold, CFT};

mod simulation;
pub use simulation::{Simulation, simulate};

mod keep_alive;
pub use keep_alive::{keep_alive_sets};

mod moves;
pub use moves::{moves};

mod allocator;
pub use allocator::{Instruction, allocate};

mod codegen;
pub use codegen::{generate_code};

/** Optimizes an [`EBB`]. */
pub fn optimize(_num_globals: usize, input: &EBB) -> EBB {
    // Generate the [`Dataflow`] graph.
    let (dataflow, cft) = simulate(input);
    // Compute the keep-alive sets.
    let _kas = keep_alive_sets(&dataflow, &cft);

    // TODO:
    // Make an initial [`Schedule`].
    // Choose the execution order and allocate [`Register`]s.
    // Generate the [`Action`]s.
    unimplemented!()
}


// TODO: Delete.
/*
/** Optimizes a basic block. */
pub fn optimize(num_globals: usize, before: &Convention, after: &Convention, actions: &[Action]) -> Box<[Action]> {
    // Generate the [`Dataflow`] graph.
    let mut simulation = Simulation::new(before);
    for action in actions {
        simulation.action(action);
    }
    let (dataflow, exit_node) = simulation.finish(after);
    // TODO: enumerate the live [`Node`]s. For now, keep them all.
    let nodes: Vec<_> = dataflow.all_nodes().collect();
    assert_eq!(dataflow.entry_node(), nodes[0]);
    let nodes = &nodes[1..];
    // Refine the schedule and allocate registers.
    let (instructions, allocation) = allocate(before, &dataflow, nodes);
    // Generate the [`Action`]s.
    generate_code(num_globals, before, after, &dataflow, &instructions, allocation, exit_node)
}
*/

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
/*
    use super::*;
    use code::{Register, REGISTERS, Slot, UnaryOp, BinaryOp, AliasMask, Precision, Width};
    use code::tests::{Emulator};

    #[test]
    fn nop() {
        let before = Convention {
            live_values: Box::new([]),
            slots_used: 0,
        };
        let actions = vec![];
        let after = Convention {
            live_values: Box::new([]),
            slots_used: 0,
        };
        let observed = optimize(0, &before, &after, &actions);
        let expected: Box<[Action]> = Box::new([]);
        assert_eq!(observed, expected);
    }

    #[test]
    fn one_ops() {
        const V0: Register = REGISTERS[0];
        const V1: Slot = Slot(0);
        let convention = Convention {
            live_values: Box::new([V0.into(), V1.into()]),
            slots_used: 1,
        };
        let emulator = Emulator::new(convention.live_values.iter().copied().collect());
        use Precision::*;
        for action in [
            Action::Constant(P64, V0, 924573497),
            Action::Unary(UnaryOp::Not, P64, V0, V1.into()),
            Action::Binary(BinaryOp::Add, P64, V0, V0.into(), V1.into()),
        ] {
            let actions = vec![action];
            let expected = emulator.execute(&actions);
            let optimized = optimize(0, &convention, &convention, &actions);
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
        const V0: Register = REGISTERS[0];
        const V1: Register = REGISTERS[1];
        let before = Convention {
            live_values: Box::new([V0.into(), V1.into()]),
            slots_used: 1,
        };
        let actions = vec![
            Action::Store(V0, V1.into(), (V0.into(), Four), AliasMask(1)),
            Action::Constant(P64, V0, 1234),
        ];
        let after = Convention {
            live_values: Box::new([V0.into()]),
            slots_used: 1,
        };
        let _ = optimize(0, &before, &after, &actions);
        // Just don't panic!
    }

    #[test]
    fn moves() {
        const V0: Register = REGISTERS[0];
        const V1: Register = REGISTERS[1];
        let before = Convention {
            live_values: Box::new([V1.into()]),
            slots_used: 1,
        };
        let actions = vec![
            Action::Move(V0.into(), V1.into()),
        ];
        let after = Convention {
            live_values: Box::new([V0.into()]),
            slots_used: 1,
        };
        let _ = optimize(0, &before, &after, &actions);
        // Just don't panic!
    }
*/
}
