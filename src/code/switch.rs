use super::{Variable, Action};

/** Represents straight-line code ending with a jump. */
pub struct Case<S> {
    /** The straight-line code. */
    pub actions: Vec<Action>,
    /** The jump. */
    pub new_state: S,
}

/** Represents a control-flow decision. `C` is the thing being chosen. */
pub enum Switch<C> {
    /**
     * If `discriminant` is `i` and `i < cases.len()` choose `cases[i]`.
     * Otherwise choose `default_`.
     */
    Index {
        discriminant: Variable,
        cases: Box<[C]>,
        default_: C,
    },
    /** Always does the same thing. */
    Always(C),
    /** Exit Mijit. */
    Halt,
}

impl<C> Switch<C> {
    pub fn new(discriminant: Variable, cases: Box<[C]>, default_: C) -> Self {
        Self::Index {discriminant, cases, default_}
    }

    pub fn if_(condition: Variable, if_true: C, if_false: C) -> Self {
        Self::new(condition, Box::new([if_false]), if_true)
    }

    pub fn always(default_: C) -> Self {
        Self::Always(default_)
    }

    /** Apply `callback` to every `C` and return a fresh `Switch`. */
    pub fn map<D>(&self, mut callback: impl FnMut(&C) -> D) -> Switch<D> {
        match self {
            Switch::Index {discriminant, cases, default_} => {
                let discriminant = discriminant.clone();
                let cases = cases.iter().map(&mut callback).collect();
                let default_ = callback(&default_);
                Switch::Index {discriminant, cases, default_}
            },
            Switch::Always(case) => Switch::Always(callback(&case)),
            Switch::Halt => Switch::Halt,
        }
    }
}
