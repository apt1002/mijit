use std::fmt::{Debug};

use super::{code, target};
use code::{Switch, EBB, Convention};

//-----------------------------------------------------------------------------

#[allow(unused)]
mod dep;
use dep::{Dep};

mod op;
use op::{Op};

mod resources;
use resources::{Resources};

mod cost;
use cost::{Cost, op_cost};

mod dataflow;
use dataflow::{Dataflow, Node};

mod cft;
use cft::{Cold, Exit, CFT};

mod simulation;
use simulation::{simulate};

mod builder;
use builder::{build};

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
    use crate::code::{REGISTERS as R, BinaryOp, builder as cb};
    use BinaryOp::*;
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

    /// Optimize `input_ebb`, emulate the original and optimized `EBB`s, and
    /// panic with diagnostics if they behave differently.
    pub fn optimize_and_compare(input_ebb: EBB<usize>, convention: Convention) {
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

    #[test]
    fn regression_0() {
        // This was once `random_ebb(0, 2)` but both have since changed.
        let ebb = cb::build(|mut b| {
            b.binary64(Xor, R[2], R[3], R[4]);
            b.binary64(Lt, R[3], R[3], R[4]);
            b.guard(R[3], false, cb::build(|b| b.jump(0)));
            b.binary64(Lt, R[2], R[2], R[2]);
            b.jump(1)
        });
        optimize_and_compare(ebb, random_ebb_convention());
    }

    #[test]
    fn regression_8() {
        // This was once `random_ebb(8, 3)` but both have since changed.
        let ebb = cb::build(|mut b| {
            b.const_binary64(Add, R[2], R[2], 0x3b386b745518224d as i64);
            b.binary64(Xor, R[4], R[2], R[4]);
            b.binary64(Lt, R[2], R[3], R[2]);
            b.guard(R[2], false, cb::build(|b| b.jump(0)));
            b.binary64(Lt, R[3], R[2], R[2]);
            b.guard(R[3], true, cb::build(|b| b.jump(1)));
            b.const_binary64(Add, R[2], R[2], 0xc531fbc2c4c7042 as i64);
            b.binary64(Xor, R[4], R[2], R[4]);
            b.guard(R[2], false, cb::build(|b| b.jump(2)));
            b.jump(3)
        });
        optimize_and_compare(ebb, random_ebb_convention());
    }

    #[test]
    fn regression_27() {
        // This was once `random_ebb(27, 2)` but both have since changed.
        let ebb = cb::build(|mut b| {
            b.const_binary64(Add, R[4], R[4], 0x523e32f31c82fa38 as i64);
            b.binary64(Xor, R[2], R[4], R[2]);
            b.binary64(Lt, R[4], R[3], R[3]);
            b.guard(R[4], true, cb::build(|b| b.jump(0)));
            b.const_binary64(Add, R[3], R[3], 0x2854088f4544aaa6 as i64);
            b.guard(R[3], false, cb::build(|b| b.jump(1)));
            b.jump(2)
        });
        optimize_and_compare(ebb, random_ebb_convention());
    }

    #[test]
    fn optimize_random_ebbs() {
        for seed in 0..1000 {
            let input_ebb = random_ebb(seed, 2);
            optimize_and_compare(input_ebb, random_ebb_convention());
        }
    }
}
