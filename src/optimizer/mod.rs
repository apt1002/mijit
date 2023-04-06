use std::fmt::{Debug};

use super::{code, target};
use code::{Switch, EBB, Convention};

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
pub use cft::{Cold, CFT};

mod simulation;
pub use simulation::{Simulation, simulate};

mod builder;
pub use builder::{build};

/// Look up information about a control-flow merge point.
pub trait LookupLeaf {
    // A control-flow merge point.
    type Leaf: Debug + Clone;
    /// Return the convention in effect at `leaf`.
    fn after(&self, leaf: &Self::Leaf) -> &Convention;
    /// Return the estimated relative frequency of `leaf`.
    fn weight(&self, leaf: &Self::Leaf) -> usize;
}

/// Optimizes an [`EBB`].
pub fn optimize<L: LookupLeaf>(before: &Convention, input: &EBB<L::Leaf>, lookup_leaf: &L)
-> EBB<L::Leaf> {
    // Generate the [`Dataflow`] graph.
    let (dataflow, cft) = simulate(before, input, lookup_leaf);
    // Turn it back into an EBB.
    build(before, &dataflow, &cft, lookup_leaf)
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::tests::{EmulatorResult, random_ebb, random_ebb_convention};

    // Several tests represent leaves as integers.
    impl LookupLeaf for Convention {
        type Leaf = usize;
        fn after(&self, _leaf: &usize) -> &Convention {
            self
        }
        fn weight(&self, leaf: &usize) -> usize {
            *leaf
        }
    }

    #[test]
    fn optimize_random_ebbs() {
        for seed in 0..1000 {
            println!("seed = {}", seed);
            let input_ebb = random_ebb(seed, 2);
            let convention = random_ebb_convention();
            let mut expected = EmulatorResult::new(&input_ebb, &convention);
            expected.keep_only(&convention.live_values);
            let output_ebb = optimize(&convention, &input_ebb, &convention);
            let mut observed = EmulatorResult::new(&output_ebb, &convention);
            observed.keep_only(&convention.live_values);
            if expected != observed {
                println!("input_ebb: {:#x?}", input_ebb);
                println!("expected: {:#x?}", expected);
                println!("output_ebb: {:#x?}", output_ebb);
                println!("observed: {:#x?}", observed);
                panic!("expected != observed");
            }
        }
    }
}
