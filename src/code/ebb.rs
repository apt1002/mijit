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
    pub actions: Vec<Action>,
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
    use rand::prelude::*;
    use rand_pcg::{Pcg64};

    use super::*;
    use super::super::{Register, REGISTERS, Convention, BinaryOp, builder};
    use BinaryOp::*;

    struct RandomEBB<R: Rng> {
        rng: R,
        regs: Vec<Register>,
        tmp: Register,
        next_leaf: usize,
    }

    impl<R: Rng> RandomEBB<R> {
        fn new(rng: R) -> Self {
            Self {
                rng,
                regs: vec![REGISTERS[0], REGISTERS[1], REGISTERS[2], REGISTERS[3]],
                tmp: REGISTERS[4],
                next_leaf: 0,
            }
        }

        /// Return a random register.
        fn rr(&mut self) -> Register {
            self.regs[self.rng.gen_range(0..self.regs.len())]
        }

        fn gen(&mut self, size: usize) -> EBB<usize> {
            let r = self.rr();
            builder::build(|mut b| {
                b.const_(self.tmp, self.rng.gen());
                b.binary64(Add, r, r, self.tmp);
                b.binary64(Xor, r, r, self.rr());
                b.binary64(Lt, self.tmp, self.rr(), self.rr());
                if size == 0 {
                    let leaf = self.next_leaf;
                    self.next_leaf += 1;
                    b.jump(leaf)
                } else {
                    let left_size = self.rng.gen_range(0..size);
                    let right_size = size - 1 - left_size;
                    b.if_(self.tmp, self.gen(left_size), self.gen(right_size))
                }
            })
        }

        fn convention(&self) -> Convention {
            Convention {
                live_values: self.regs.iter().map(|&r| Variable::from(r)).collect(),
                slots_used: 0,
            }
        }
    }

    /// Return a deterministically random EBB.
    /// The Convention is used on entry, and on every exit. The exits are
    /// numbered.
    pub fn random_ebb(seed: u64) -> (EBB<usize>, Convention) {
        let mut random_ebb = RandomEBB::new(Pcg64::seed_from_u64(seed));
        (
            random_ebb.gen(4),
            random_ebb.convention(),
        )
    }

    #[test]
    fn generate_ebb() {
        let _ = random_ebb(0);
    }
}
