use super::code::{Action};
use super::jit::{Convention};

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
    use super::super::{code};
    use code::{Register, UnaryOp, BinaryOp, Precision};
    use code::tests::{Emulator};
    use super::super::jit::lowerer::{ALLOCATABLE_REGISTERS};

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
