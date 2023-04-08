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
            live_values: REGS.iter().map(|&r| Variable::from(r)).collect(),
            slots_used: 0,
        }
    }

    #[test]
    fn generate_ebb() {
        let _ = random_ebb(0, 10);
    }
}
