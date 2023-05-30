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

    /// Apply `callback` to every `C` and return a fresh `Switch`.
    pub fn map_once<D>(self, mut callback: impl FnMut(C) -> D) -> Switch<D> {
        Switch {
            cases: Vec::from(self.cases).into_iter().map(&mut callback).collect(),
            default_: Box::new(callback(*self.default_)),
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
