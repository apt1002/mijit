use std::collections::{HashMap};

use super::code::{self, Action};
use super::jit::{Convention};
use super::jit::lowerer::{ALLOCATABLE_REGISTERS, TEMP_VALUE};

mod dataflow;
pub use dataflow::{Node, Op, Simulation};

mod pressure;
pub use pressure::{Life, Pressure};

mod schedule;
pub use schedule::{Schedule, Time, EARLY, LATE};

mod moves;
pub use moves::{moves};

mod allocation;
pub use allocation::{Allocation};


/** Optimizes a basic block. */
pub fn optimize(
    before: &Convention,
    actions: &[Action],
    after: &Convention,
) -> Vec<Action> {
    // 1. Simulation.
    let mut simulation = Simulation::new(&before.live_values);
    for action in actions {
        simulation.action(action);
    }
    // 2. Schedule.
    let roots: Vec<_> = after.live_values.iter()
        .map(|&value| simulation.lookup(value))
        .chain(simulation.implicit_dependencies())
        .map(|node| (node, LATE))
        .collect();
    let schedule = Schedule::new(roots);
    // 3. Match `before`.
    // TODO: choose a logical-to-physical register mapping to avoid moves.
    // 4. Allocation.
    let slots_used = std::cmp::max(before.slots_used, after.slots_used);
    let mut allocation = Allocation::new(ALLOCATABLE_REGISTERS /* TODO: 3. */, slots_used);
    let mut dest_to_src = HashMap::new();
    for (node, _, register) in schedule.inputs() {
        let (dest, src) = allocation.input(node.clone(), register);
        if let Some(_old) = dest_to_src.insert(dest, src) { panic!("Two Inputs in the same register"); }
    }
    for (dest, src) in moves(dest_to_src, TEMP_VALUE) {
        allocation.actions.push(Action::Move(dest, src));
    }
    for (node, _, register) in schedule.iter() {
        allocation.node(node.clone(), register);
    }
    // 5. Match `after`.
    let dest_to_src: HashMap<_, _> = after.live_values.iter().map(|&dest| {
        let node = simulation.lookup(dest);
        let src = allocation.lookup(&node);
        (dest, src)
    }).collect();
    for (dest, src) in moves(dest_to_src, TEMP_VALUE) {
        allocation.actions.push(Action::Move(dest, src));
    }
    // Return.
    allocation.actions
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{code};
    use code::{Value, UnaryOp, BinaryOp, Precision};
    use code::tests::{Emulator};
    use rand::{self, SeedableRng};
    use rand::distributions::{Distribution, Uniform};

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
    fn moves() {
        const NUM_TESTS: usize = 1000;
        const NUM_MOVES: usize = 5;
        // We will use these Values.
        let values = vec![
            Value::Slot(0),
            Value::Slot(2),
            Value::Register(ALLOCATABLE_REGISTERS[8]),
            Value::Register(ALLOCATABLE_REGISTERS[9]),
        ];
        // All our Values are live.
        let convention = Convention {
            live_values: values.clone(),
            slots_used: 3,
        };
        // Generate random Values from our list.
        let mut rng = rand::rngs::StdRng::seed_from_u64(0);
        let mut random_value = || {
            values[Uniform::new(0, values.len()).sample(&mut rng)].clone()
        };
        // Generate and test some random code sequences.
        let emulator = Emulator::new(values.clone());
        for _ in 0..NUM_TESTS {
            let actions: Vec<_> = (0..NUM_MOVES).map(|_| {
                Action::Move(random_value(), random_value())
            }).collect();
            let expected = emulator.execute(&actions);
            let optimized = optimize(&convention, &actions, &convention);
            let observed_with_temporaries = emulator.execute(&optimized);
            let observed: HashMap<_, _> = values.iter().map(|&value| {
                let c = *observed_with_temporaries.get(&value).expect("Missing Value");
                (value, c)
            }).collect();
            if expected != observed {
                println!("actions = {:#?}", actions);
                println!("expected = {:#?}", expected);
                println!("observed = {:#?}", observed);
                panic!("Optimized code does not do the same thing as the original");
            }
        }
    }

    #[test]
    fn one_ops() {
        const R0: Value = Value::Register(ALLOCATABLE_REGISTERS[0]);
        const R1: Value = Value::Register(ALLOCATABLE_REGISTERS[1]);
        let convention = Convention {
            live_values: vec![R0, R1],
            slots_used: 0,
        };
        let emulator = Emulator::new(convention.live_values.clone());
        use Precision::*;
        for action in &[
            Action::Constant(P64, R0, 924573497),
            Action::Unary(UnaryOp::Not, P64, R0, R1),
            Action::Binary(BinaryOp::Add, P64, R0, R0, R1),
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
