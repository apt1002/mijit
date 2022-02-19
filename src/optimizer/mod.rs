use std::fmt::{Debug};
use super::{code, target};

use code::{Convention, EBB};

//-----------------------------------------------------------------------------

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

mod builder;
pub use builder::{build};

/** Look up information about a control-flow merge point. */
pub trait LookupLeaf<L: Clone> {
    /** Return the convention in effect at `leaf`. */
    fn after(&self, leaf: &L) -> &Convention;
    /** Return the estimated relative frequency of `leaf`. */
    fn weight(&self, leaf: &L) -> usize;
}

/** Optimizes an [`EBB`]. */
pub fn optimize<L: Clone + Debug>(before: &Convention, input: &EBB<L>, lookup_leaf: &impl LookupLeaf<L>)
-> EBB<L> {
    // Generate the [`Dataflow`] graph.
    let (dataflow, cft) = simulate(before, input, lookup_leaf);
    build(before, &dataflow, &cft, lookup_leaf)
}

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
