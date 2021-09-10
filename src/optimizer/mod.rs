use super::code::{self, Register, Convention, Action};

const NUM_REGISTERS: usize = super::target::x86_64::ALLOCATABLE_REGISTERS.len();

fn all_registers() -> impl Iterator<Item=Register> {
    (0..NUM_REGISTERS).map(|i| Register::new(i as u8).unwrap())
}

//-----------------------------------------------------------------------------

mod op;
pub use op::{Op};

mod resources;
pub use resources::{Resources};

mod cost;
pub use cost::{BUDGET, SPILL_COST, SLOT_COST, Cost, op_cost};

mod dataflow;
pub use dataflow::{Dataflow, Node, Out};

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

mod allocator;
pub use allocator::{Instruction, Allocator};

mod codegen;
pub use codegen::{CodeGen};

/** Optimizes a basic block. */
pub fn optimize(num_globals: usize, before: &Convention, after: &Convention, actions: &[Action]) -> Box<[Action]> {
    // Generate the [`Dataflow`] graph.
    let mut simulation = Simulation::new(before);
    for action in actions {
        simulation.action(action);
    }
    let (dataflow, exit_node) = simulation.finish(after);
    // Make an initial [`Schedule`].
    let nodes: Vec<_> = dataflow.all_nodes().collect(); // TODO.
    assert_eq!(dataflow.entry_node(), nodes[0]);
    assert_eq!(exit_node, nodes[nodes.len()-1]);
    let nodes = &nodes[1..nodes.len()-1];
    let schedule = Schedule::new(&dataflow, nodes, exit_node);
    // Choose the execution order and allocate [`Register`]s.
    let mut allocator = Allocator::new(before, schedule);
    while let Some(node) = allocator.next() {
        allocator.add_node(node);
    }
    let (instructions, allocation) = allocator.finish();
    // Generate the [`Action`]s.
    let mut codegen = CodeGen::new(num_globals, before, &dataflow, allocation);
    for i in instructions {
        match i {
            Instruction::Absent => panic!("Absent instruction"),
            Instruction::Spill(out1, out2) => codegen.add_spill(out1, out2),
            Instruction::Node(n) => codegen.add_node(n),
        }
    }
    codegen.finish(after, exit_node)
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::{HashMap};
    use super::*;
    use code::{Register, REGISTERS, Slot, UnaryOp, BinaryOp, AliasMask, Precision, Width};
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
        let observed = optimize(0, &before, &after, &actions);
        let expected: Box<[Action]> = Box::new([]);
        assert_eq!(observed, expected);
    }

    #[test]
    fn one_ops() {
        const V0: Register = REGISTERS[0];
        const V1: Slot = Slot(0);
        let convention = Convention {
            live_values: vec![V0.into(), V1.into()],
            slots_used: 1,
        };
        let emulator = Emulator::new(convention.live_values.clone());
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
            live_values: vec![V0.into(), V1.into()],
            slots_used: 1,
        };
        let actions = vec![
            Action::Store(V0, V1.into(), (V0.into(), Four), AliasMask(1)),
            Action::Constant(P64, V0, 1234),
        ];
        let after = Convention {
            live_values: vec![V0.into()],
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
            live_values: vec![V1.into()],
            slots_used: 1,
        };
        let actions = vec![
            Action::Move(V0.into(), V1.into()),
        ];
        let after = Convention {
            live_values: vec![V0.into()],
            slots_used: 1,
        };
        let _ = optimize(0, &before, &after, &actions);
        // Just don't panic!
    }
}
