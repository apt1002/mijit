use std::collections::{HashSet};

use super::code::{GLOBAL, Variable, IntoVariable, Action, Switch};

/// Represents the convention by which code passes values to a label. The
/// concept is similar to a calling convention, but it's for a jump, not a
/// call.
#[derive(Debug, Clone)]
pub struct Convention {
    /// The values that are live on entry.
    pub lives: Box<[Variable]>,
    /// The number of spill [`Slot`]s used by the `Convention`.
    ///
    /// [`Slot`]: super::Slot
    pub slots_used: usize,
}

impl Convention {
    /// Checks whether code using `old` can jump to code using `self`.
    /// All [`Variable`]s live in `self` must also be live in `old`, and
    /// `self` and `old` must have the same `slots_used`.
    pub fn refines(&self, old: &Self) -> bool {
        let old_lives: HashSet<Variable> = old.lives.iter().copied().collect();
        self.lives.iter().all(|v| old_lives.contains(v)) && self.slots_used == old.slots_used
    }
}

impl Default for Convention {
    /// Returns a `Convention` with no [`Slot`]s and only [`GLOBAL`] alive.
    fn default() -> Self {
        Convention {lives: Box::new([GLOBAL.into()]), slots_used: 0}
    }
}

//-----------------------------------------------------------------------------

/// A utility for computing [`Convention`]s. Given the `Convention` at the end
/// of a piece of code, this utility can calculate the `Convention` at the
/// beginning.
pub struct Propagator {
    /// The [`Variable`]s that are live.
    lives: HashSet<Variable>,
    /// The number of spill [`Slot`]s that are allocated.
    ///
    /// [`Slot`]: super::Slot
    slots_used: usize,
}

impl Propagator {
    /// Constructs a Propagator given the [`Convention`] after the code.
    pub fn new(after: &Convention) -> Self {
        Self {
            lives: after.lives.iter().copied().collect(),
            slots_used: after.slots_used,
        }
    }

    /// Adds `src` to `lives`.
    pub fn insert(&mut self, src: impl IntoVariable) {
        self.lives.insert(src.into());
    }

    /// Removes `dest` from `lives`.
    pub fn remove(&mut self, dest: impl IntoVariable) {
        self.lives.remove(&dest.into());
    }

    /// Propagate information backwards through a conditional branch.
    /// [`Variable`]s live in `other` are added to `lives`.
    pub fn branch(&mut self, other: &Convention) {
        for &v in other.lives.iter() {
            self.insert(v);
        }
        assert_eq!(self.slots_used, other.slots_used);
    }

    /// Propagate information backwards through a `Switch`.
    /// [`Variable`]s live in every case of `switch` are included in
    /// `lives`, along with `discriminant`.
    pub fn switch<'a, C>(
        discriminant: Variable,
        switch: &'a Switch<C>,
        to_convention: impl Fn(&C)-> &'a Convention,
    ) -> Self {
        let mut ret: Option<Self> = None;
        switch.map(|c| {
            let convention = to_convention(c);
            if let Some(ref mut ret) = ret {
                ret.branch(convention);
            } else {
                ret = Some(Self::new(convention));
            }
        });
        let mut ret = ret.expect("Switch has no cases");
        ret.insert(discriminant);
        ret
    }

    /// Propagate information backwards through `action`.
    /// [`Variable`]s written by `action` are removed from `lives`
    /// and those read by it are added.
    pub fn action(&mut self, action: Action) {
        use Action::*;
        match action {
            Move(dest, src) => {
                self.remove(dest);
                self.insert(src);
            },
            Constant(_, dest, _) => {
                self.remove(dest);
            },
            Unary(_, _, dest, src) => {
                self.remove(dest);
                self.insert(src);
            },
            Binary(_, _, dest, src1, src2) => {
                self.remove(dest);
                self.insert(src1);
                self.insert(src2);
            },
            Load(dest, addr) => {
                self.remove(dest);
                self.insert(addr.base);
            },
            Store(dest, src, addr) => {
                self.remove(dest);
                self.insert(src);
                self.insert(addr.base);
            },
            Send(dest, src1, src2) => {
                self.remove(dest);
                self.insert(src1);
                self.insert(src2);
            },
            Push(src1, src2) => {
                if let Some(src) = src1 {
                    self.insert(src);
                }
                if let Some(src) = src2 {
                    self.insert(src);
                }
                self.slots_used -= 2;
            },
            Drop(n) => {
                self.slots_used += 2 * n;
            },
            Debug(src) => {
                self.insert(src);
            },
        }
    }

    /// Returns the [`Convention`] before the code.
    pub fn before(&self) -> Convention {
        Convention {
            lives: self.lives.iter().copied().collect(),
            slots_used: self.slots_used,
        }
    }
}
