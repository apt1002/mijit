use std::fmt::{Debug};

use super::{code, graph, target};
use code::{Register};
use graph::{Convention};

//-----------------------------------------------------------------------------

mod simulation;
pub use simulation::{simulate};

mod fill;
use fill::{Frontier, Fill};

mod allocator;
use allocator::{Instruction, allocate};

mod moves;
use moves::{moves};

mod codegen;
use codegen::{CodeGen};

mod walker;
pub use walker::{cft_to_ebb};

//-----------------------------------------------------------------------------

const NUM_REGISTERS: usize = target::x86_64::ALLOCATABLE_REGISTERS.len();

fn all_registers() -> impl Iterator<Item=Register> {
    (0..NUM_REGISTERS).map(|i| Register::new(i as u8).unwrap())
}

//-----------------------------------------------------------------------------

/// Look up information about a control-flow merge point.
pub trait LookupLeaf {
    // A control-flow merge point.
    type Leaf: Debug + Clone;
    /// Return the convention in effect at `leaf`.
    fn after(&self, leaf: &Self::Leaf) -> &Convention;
    /// Return the estimated relative frequency of `leaf`.
    fn weight(&self, leaf: &Self::Leaf) -> usize;
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use std::fmt::{Debug};
    use std::collections::{HashMap};

    use rand::prelude::*;
    use rand_pcg::{Pcg64};

    use super::*;
    use code::{
        Register, REGISTERS as R, Variable, IntoVariable,
        Precision, BinaryOp, UnaryOp, Action, Switch, EBB, Ending,
        build,
    };
    use BinaryOp::*;
    use graph::{Dataflow, Node};
    use crate::util::{reverse_map};

    /// A subset of `REGISTERS` that differ from `code::builder::TEMP`.
    const REGS: [Register; 4] = [R[1], R[2], R[3], R[4]];

    /// Return a random register from `REGS`.
    fn rr<R: Rng>(rng: &mut R) -> Register {
        REGS[rng.gen_range(1..REGS.len())]
    }

    /// Return a deterministically random EBB.
    /// `random_ebb_convention()` is used on entry, and on every exit.
    /// The exits are numbered sequentially from `0` to `size`.
    pub fn random_ebb(seed: u64, size: usize) -> EBB<usize> {
        let rng = &mut Pcg64::seed_from_u64(seed);
        build(|mut b| {
            for leaf in 0..size {
                let r = rr(rng);
                b.const_binary64(Add, r, r, rng.gen());
                b.binary64(Xor, rr(rng), r, rr(rng));
                b.binary64(Lt, r, rr(rng), rr(rng));
                b.guard(r, rng.gen(), build(|b| b.jump(leaf)));
            }
            b.jump(size)
        })
    }

    pub fn random_ebb_convention() -> Convention {
        Convention {
            lives: REGS.iter().map(|&r| Variable::from(r)).collect(),
            slots_used: 0,
        }
    }

    #[test]
    fn generate_ebb() {
        let _ = random_ebb(0, 10);
    }

    /// An emulator for a subset of Mijit code, useful for testing
    /// automatically-generated code.
    #[derive(Debug, PartialEq)]
    pub struct Emulator {
        pub variables: HashMap<Variable, i64>,
        pub stack: Vec<i64>,
    }

    impl Emulator {
        /// Construct an [`Emulator`] with initial stack and [`Variable`]s.
        pub fn new(variables: HashMap<Variable, i64>, stack: Vec<i64>) -> Self {
            Emulator {variables, stack}
        }

        /// Read a [`Variable`].
        fn get(&self, v: impl IntoVariable) -> i64 {
            *self.variables.get(&v.into()).expect("Missing from variables")
        }

        /// Write a [`Variable`].
        fn set(&mut self, v: impl IntoVariable, x: i64) {
            self.variables.insert(v.into(), x);
        }

        /// Emulate execution of `action`.
        pub fn action(&mut self, action: &Action) {
            match action {
                &Action::Move(dest, src) => {
                    let x = self.get(src);
                    self.set(dest, x);
                },
                &Action::Constant(Precision::P64, dest, imm) => {
                    self.set(dest, imm);
                },
                &Action::Unary(op, Precision::P64, dest, src) => {
                    let x = self.get(src);
                    let result = match op {
                        UnaryOp::Not => !x,
                        _ => panic!("Don't know how to execute {:#?}", op),
                    };
                    self.set(dest, result);
                },
                &Action::Binary(op, Precision::P64, dest, src1, src2) => {
                    let x = self.get(src1);
                    let y = self.get(src2);
                    let result = match op {
                        BinaryOp::Add => x.wrapping_add(y),
                        BinaryOp::Xor => x ^ y,
                        BinaryOp::Lt => if x < y { !0 } else { 0 },
                        _ => panic!("Don't know how to execute {:#?}", op),
                    };
                    self.set(dest, result);
                },
                _ => panic!("Don't know how to execute {:#?}", action),
            }
        }

        // Emulate execution of `ebb`.
        pub fn ebb<L: Clone>(&mut self, mut ebb: &EBB<L>) -> L {
            loop {
                for action in &*ebb.actions {
                    self.action(action);
                }
                match &ebb.ending {
                    &Ending::Leaf(ref leaf) => return leaf.clone(),
                    &Ending::Switch(v, ref s) => {
                        let discriminant = self.get(v) as usize;
                        let Switch {cases, default_} = s;
                        ebb = if discriminant < cases.len() {
                            &cases[discriminant]
                        } else {
                            &default_
                        };
                    },
                }
            }
        }
    }

    #[derive(Debug, PartialEq)]
    pub struct EmulatorResult<L: Debug + Clone> {
        pub emulator: Emulator,
        pub leaf: L,
    }

    /// Run `ebb`, passing pseudo-random values for all `Variable`s live
    /// according to `convention`, keeping only the results live according to
    /// `convention`, and return the result.
    fn emulate<L: Debug + Clone>(ebb: &EBB<L>, convention: &Convention) -> EmulatorResult<L> {
        let variables: HashMap<Variable, i64> = convention.lives.iter().enumerate()
            .map(|(i, &v)| {
                (v, (i as i64).wrapping_mul(0x4afe41af6db32983).wrapping_add(0x519e8556c7b69a8d))
            }).collect();
        let mut emulator = Emulator::new(variables, vec![]);
        let leaf = emulator.ebb(ebb);
        // Keep in `emulator.variables` only those in `convention`.
        emulator.variables = convention.lives.iter().filter_map(
            |&v| emulator.variables.get(&v).map(|&x| (v, x))
        ).collect();
        EmulatorResult {emulator, leaf}
    }

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
        let expected = emulate(&input_ebb, &convention);
        // Temporary: generate the [`Dataflow`] graph.
        let mut dataflow = Dataflow::new(convention.lives.len());
        let input_map: HashMap<Node, Variable> =
            dataflow.inputs().iter()
            .zip(convention.lives.iter())
            .map(|(&node, &variable)| (node, variable))
            .collect();
        let cft = simulate(&mut dataflow, convention.slots_used, reverse_map(&input_map), &input_ebb, &convention);
        // Optimize.
        let output_ebb = cft_to_ebb(&dataflow, convention.slots_used, &input_map, &cft, &convention);
        // Execute.
        let observed = emulate(&output_ebb, &convention);
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
        let ebb = build(|mut b| {
            b.binary64(Xor, R[2], R[3], R[4]);
            b.binary64(Lt, R[3], R[3], R[4]);
            b.guard(R[3], false, build(|b| b.jump(0)));
            b.binary64(Lt, R[2], R[2], R[2]);
            b.jump(1)
        });
        optimize_and_compare(ebb, random_ebb_convention());
    }

    #[test]
    fn regression_8() {
        // This was once `random_ebb(8, 3)` but both have since changed.
        let ebb = build(|mut b| {
            b.const_binary64(Add, R[2], R[2], 0x3b386b745518224d as i64);
            b.binary64(Xor, R[4], R[2], R[4]);
            b.binary64(Lt, R[2], R[3], R[2]);
            b.guard(R[2], false, build(|b| b.jump(0)));
            b.binary64(Lt, R[3], R[2], R[2]);
            b.guard(R[3], true, build(|b| b.jump(1)));
            b.const_binary64(Add, R[2], R[2], 0xc531fbc2c4c7042 as i64);
            b.binary64(Xor, R[4], R[2], R[4]);
            b.guard(R[2], false, build(|b| b.jump(2)));
            b.jump(3)
        });
        optimize_and_compare(ebb, random_ebb_convention());
    }

    #[test]
    fn regression_27() {
        // This was once `random_ebb(27, 2)` but both have since changed.
        let ebb = build(|mut b| {
            b.const_binary64(Add, R[4], R[4], 0x523e32f31c82fa38 as i64);
            b.binary64(Xor, R[2], R[4], R[2]);
            b.binary64(Lt, R[4], R[3], R[3]);
            b.guard(R[4], true, build(|b| b.jump(0)));
            b.const_binary64(Add, R[3], R[3], 0x2854088f4544aaa6 as i64);
            b.guard(R[3], false, build(|b| b.jump(1)));
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
