use std::cmp::{Ordering};

/// How a [`Node`] uses a value computed by another `Node`
/// None of these imply that the `Node`s have to be executed in order.
///
/// [`Node`]: super::Node
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Value {
    /// The value is not needed so may be discarded.
    Unused = 0,
    /// The value is needed but not as a memory address.
    Normal = 2,
    /// The value is needed to access the memory it points to.
    Address = 3,
}

/// How a [`Node`] depends on side-effects of a previous `Node`.
/// None of these imply that the computed value is needed.
///
/// [`Node`]: super::Node
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Effect {
    /// The `Node` is a guard. It is proxying a dependency is on a cold path.
    /// The `Node`s can be executed in either order. If necessary, the other
    /// `Node` can be executed on the cold path.
    Cold = 0,
    /// The dependency is entirely on the hot path.
    /// The `Node` must wait for the other `Node` to be executed.
    Hot = 1,
    /// The other `Node` computes a pointer.
    /// The `Node` must wait for all memory accesses via that pointer.
    Send = 2,
}

/// Annotates a dependency of a [`Node`] on a previous `Node`.
///
/// Constants are provided for all useful `Dep` values:
///
/// ```text
///       | Unused  Normal      Address
/// ------+---------------------------------
/// Cold  | NONE    COLD_VALUE  COLD_LOAD
/// Hot   | GUARD   VALUE       LOAD
/// Send  | SEND                STORE
/// ```
///
/// [`Node`]: super::Node
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Dep(pub Value, pub Effect);

impl PartialOrd for Dep {
    /// Tests whether `self` is a stronger dependency that `other`.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Ordering::*;
        match (self.0.cmp(&other.0), self.1.cmp(&other.1)) {
            (Less, Greater) | (Greater, Less) => None,
            (Equal, ordering) => Some(ordering),
            (ordering, _) => Some(ordering),
        }
    }
}

impl std::ops::BitOr for Dep {
    type Output = Self;

    /// Computes the least upper bound of `self` and `other`.
    fn bitor(self, other: Self) -> Self {
        Self(self.0.max(other.0), self.1.max(other.1))
    }
}

pub const NONE: Dep = Dep(Value::Unused, Effect::Cold);
pub const COLD_VALUE: Dep = Dep(Value::Normal, Effect::Cold);
pub const COLD_LOAD: Dep = Dep(Value::Address, Effect::Cold);
pub const GUARD: Dep = Dep(Value::Unused, Effect::Hot);
pub const VALUE: Dep = Dep(Value::Normal, Effect::Hot);
pub const LOAD: Dep = Dep(Value::Address, Effect::Hot);
pub const SEND: Dep = Dep(Value::Unused, Effect::Send);
pub const STORE: Dep = Dep(Value::Address, Effect::Send);






//-----------------------------------------------------------------------------

