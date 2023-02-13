use super::{Action};

/// Represents straight-line code ending with a jump.
#[derive(Debug, Clone)]
pub struct Case<S> {
    /// The straight-line code.
    pub actions: Vec<Action>,
    /// The jump.
    pub new_state: S,
}

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
    pub fn map<D>(&self, mut callback: impl FnMut(&C) -> D) -> Switch<D> {
        let cases = self.cases.iter().map(&mut callback).collect();
        let default_ = Box::new(callback(&self.default_));
        Switch {cases, default_}
    }
}
