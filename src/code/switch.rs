use super::{Variable, Action};

/** Represents straight-line code ending with a jump. */
#[derive(Debug, Clone)]
pub struct Case<S> {
    /** The straight-line code. */
    pub actions: Vec<Action>,
    /** The jump. */
    pub new_state: S,
}

/** Represents a control-flow decision. `C` is the thing being chosen. */
#[derive(Debug, Clone)]
pub enum Switch<C> {
    /**
     * If `discriminant` is `i` and `i < cases.len()` choose `cases[i]`.
     * Otherwise choose `default_`.
     */
    Index {
        discriminant: Variable,
        cases: Box<[C]>,
        default_: Box<C>,
    },
    /** Always does the same thing. */
    Always(Box<C>),
}

impl<C> Switch<C> {
    pub fn new(discriminant: Variable, cases: Box<[C]>, default_: C) -> Self {
        Self::Index {discriminant, cases, default_: Box::new(default_)}
    }

    pub fn if_(condition: Variable, if_true: C, if_false: C) -> Self {
        Self::new(condition, Box::new([if_false]), if_true)
    }

    pub fn always(default_: C) -> Self {
        Self::Always(Box::new(default_))
    }

    pub fn discriminant(&self) -> Option<Variable> {
        match self {
            Switch::Index {discriminant, ..} => Some(*discriminant),
            Switch::Always(_) => None,
        }
    }

    /** Apply `callback` to every `C` and return a fresh `Switch`. */
    pub fn map<D>(&self, mut callback: impl FnMut(&C) -> D) -> Switch<D> {
        match self {
            Switch::Index {discriminant, cases, default_} => {
                let discriminant = *discriminant;
                let cases = cases.iter().map(&mut callback).collect();
                let default_ = Box::new(callback(&*default_));
                Switch::Index {discriminant, cases, default_}
            },
            Switch::Always(case) => Switch::Always(Box::new(callback(&*case))),
        }
    }
}
