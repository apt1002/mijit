use super::{Variable, Action};

/// Represents a control-flow decision. `C` is the thing being chosen.
/// If the discriminant is `i` and `i < cases.len()` choose `cases[i]`.
/// Otherwise choose `default_`.
#[derive(Debug, Clone)]
pub struct Switch<C> {
    pub cases: Box<[C]>,
    pub default_: Box<C>,
}

impl<C> Switch<C> {
    pub fn new(cases: Box<[C]>, default_: C) -> Self {
        Self {cases, default_: Box::new(default_)}
    }

    pub fn if_(if_true: C, if_false: C) -> Self {
        Self::new(Box::new([if_false]), if_true)
    }

    /// Apply `callback` to every `C` and return a fresh `Switch`.
    pub fn map<'a, D>(&'a self, mut callback: impl FnMut(&'a C) -> D) -> Switch<D> {
        Switch {
            cases: self.cases.iter().map(&mut callback).collect(),
            default_: Box::new(callback(&self.default_)),
        }
    }
}

/// Represents an [extended basic block], i.e. a tree-like control-flow graph.
///
/// `L` identifies a point where control-flow merges with pre-existing code.
///
/// [extended basic block]: https://en.wikipedia.org/wiki/Extended_basic_block
#[derive(Debug, Clone)]
pub struct EBB<L> {
    pub actions: Box<[Action]>,
    pub ending: Ending<L>,
}

#[derive(Debug, Clone)]
pub enum Ending<L> {
    /// Control-flow merges with pre-existing code.
    Leaf(L),
    /// Control-flow diverges.
    Switch(Variable, Switch<EBB<L>>),
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use std::fmt::{Debug};
    use std::collections::{HashMap, HashSet};

    use rand::prelude::*;
    use rand_pcg::{Pcg64};

    use super::*;
    use super::super::{
        Register, REGISTERS, Variable, IntoVariable, Convention,
        Precision, BinaryOp, UnaryOp, builder,
    };
    use BinaryOp::*;

    /// A subset of `REGISTERS` that differ from `builder::TEMP`.
    const REGS: [Register; 4] = [REGISTERS[1], REGISTERS[2], REGISTERS[3], REGISTERS[4]];

    /// Return a random register from `REGS`.
    fn rr<R: Rng>(rng: &mut R) -> Register {
        REGS[rng.gen_range(1..REGS.len())]
    }

    /// Return a deterministically random EBB.
    /// `random_ebb_convention()` is used on entry, and on every exit.
    /// The exits are numbered sequentially from `0` to `size`.
    pub fn random_ebb(seed: u64, size: usize) -> EBB<usize> {
        let rng = &mut Pcg64::seed_from_u64(seed);
        builder::build(|mut b| {
            for leaf in 0..size {
                let r = rr(rng);
                b.const_binary64(Add, r, r, rng.gen());
                b.binary64(Xor, rr(rng), r, rr(rng));
                b.binary64(Lt, r, rr(rng), rr(rng));
                b.guard(r, rng.gen(), builder::build(|b| b.jump(leaf)));
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

    impl<L: Debug + Clone> EmulatorResult<L> {
        /// Run `ebb`, passing random values for all `Variable`s live
        /// according to `convention`, and return the result.
        pub fn new(ebb: &EBB<L>, convention: &Convention) -> Self {
            let variables: HashMap<Variable, i64> = convention.lives.iter().enumerate()
                .map(|(i, &v)| {
                    (v, (i as i64).wrapping_mul(0x4afe41af6db32983).wrapping_add(0x519e8556c7b69a8d))
                }).collect();
            let mut emulator = Emulator::new(variables, vec![]);
            let leaf = emulator.ebb(ebb);
            EmulatorResult {emulator, leaf}
        }

        /// Remove from `self.emulator.variables` all those `Variable`s not
        /// in `variables`.
        pub fn keep_only(&mut self, variables: &[Variable]) {
            let variables: HashSet<_> = variables.iter().cloned().collect();
            self.emulator.variables = self.emulator.variables.iter().filter_map(|(&v, &x)| {
                if variables.contains(&v) {
                    Some((v, x))
                } else {
                    None
                }
            }).collect();
        }
    }
}
