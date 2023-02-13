use super::{Variable, Action};

/// Represents straight-line code ending with a jump.
#[derive(Debug, Clone)]
pub struct Case<S> {
    /// The straight-line code.
    pub actions: Vec<Action>,
    /// The jump.
    pub new_state: S,
}

/// Represents a control-flow decision. `C` is the thing being chosen.
/// If `discriminant` is `i` and `i < cases.len()` choose `cases[i]`.
/// Otherwise choose `default_`.
#[derive(Debug, Clone)]
pub struct Switch<C> {
    pub discriminant: Variable,
    pub cases: Box<[C]>,
    pub default_: Box<C>,
}

impl<C> Switch<C> {
    pub fn new(discriminant: Variable, cases: Box<[C]>, default_: C) -> Self {
        Self {discriminant, cases, default_: Box::new(default_)}
    }

    pub fn if_(condition: Variable, if_true: C, if_false: C) -> Self {
        Self::new(condition, Box::new([if_false]), if_true)
    }

    /// Apply `callback` to every `C` and return a fresh `Switch`.
    pub fn map<D>(&self, mut callback: impl FnMut(&C) -> D) -> Switch<D> {
        let discriminant = self.discriminant;
        let cases = self.cases.iter().map(&mut callback).collect();
        let default_ = Box::new(callback(&self.default_));
        Switch {discriminant, cases, default_}
    }
}
