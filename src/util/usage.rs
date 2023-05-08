use std::cmp::{PartialEq};
use std::collections::{HashMap};
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

use super::{First, Map};

array_index! {
    /// An index into a `Usage`.
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Use(std::num::NonZeroUsize) {
        debug_name: "Use",
        UInt: usize,
    }
}

/// A stack of `(T, U)` which, for each `t: T`, remembers the position of the
/// topmost item with an equal `t`.
#[derive(Clone)]
pub struct Usage<T: Clone + Hash + Eq, U> {
    /// The stack items. The first occurrence of `t` is stored as `(t, None)`.
    /// Each subsequent occurence is stored as `(t, Some(use))` where `use` is
    /// the previous occurrence of `t`.
    ts: Vec<((T, U), Option<Use>)>,
    /// The most recent occurrence of each `t`.
    tops: HashMap<T, Use>,
}

impl<T: Clone + Hash + Eq, U> Usage<T, U> {
    /// Returns the number of items on this stack.
    pub fn len(&self) -> usize { self.ts.len() }

    pub fn is_empty(&self) -> bool { self.ts.is_empty() }

    /// Yields borrows of the `T`s on this stack.
    pub fn iter(&self) -> <&Self as IntoIterator>::IntoIter {
        self.into_iter()
    }

    /// Returns `len()` wrapped as a `Use`.
    fn top(&self) -> Use {
        Use::new(self.ts.len()).expect("Overflow")
    }

    /// Appends an item to this stack.
    pub fn push(&mut self, t: T, u: U) {
        let prev = self.tops.insert(t.clone(), self.top());
        self.ts.push(((t, u), prev));
    }

    /// Removes the most recently [`push()`]ed item, if any.
    ///
    /// [`push()`]: Self::push
    pub fn pop(&mut self) -> Option<(T, U)> {
        self.ts.pop().map(|((t, u), prev)| {
            let top = if let Some(mut top) = prev {
                std::mem::swap(&mut top, self.tops.get_mut(&t).expect("Missing top"));
                top
            } else {
                self.tops.remove(&t).expect("Missing top")
            };
            assert_eq!(top, self.top());
            (t, u)
        })
    }

    /// Returns the index of the topmost occurence of `t` on this stack,
    /// defined to be the number of items pushed before it.
    pub fn topmost(&self, t: &T) -> Option<Use> { self.tops.get(t).copied() }
}

impl<T: Clone + Hash + Eq, U> Default for Usage<T, U> {
    fn default() -> Self {
        Self {ts: Vec::new(), tops: HashMap::new()}
    }
}

impl<T: Debug + Clone + Hash + Eq, U: Debug> Debug for Usage<T, U> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Clone + Hash + Eq, U> IntoIterator for Usage<T, U> {
    type Item = (T, U);
    type IntoIter = Map<std::vec::IntoIter<((T, U), Option<Use>)>, First>;

    fn into_iter(self) -> Self::IntoIter {
        Map(self.ts.into_iter(), First)
    }
}

impl<'a, T: Clone + Hash + Eq, U> IntoIterator for &'a Usage<T, U> {
    type Item = &'a (T, U);
    type IntoIter = Map<std::slice::Iter<'a, ((T, U), Option<Use>)>, First>;

    fn into_iter(self) -> Self::IntoIter {
        Map(self.ts.iter(), First)
    }
}

impl<T: Clone + Hash + Eq, U: Hash + Eq> Hash for Usage<T, U> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for (t, u) in self { (t, u).hash(state); }
    }
}

impl<T: Clone + Hash + Eq, U: PartialEq> PartialEq for Usage<T, U> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(x, y)| x == y)
    }
}

impl<T: Clone + Hash + Eq, U, V, W> PartialEq<V> for Usage<T, U> where
    V: std::ops::Deref<Target=[W]>,
    (T, U): PartialEq<W>,
{
    fn eq(&self, other: &V) -> bool {
        self.iter().zip(other.iter()).all(|(x, y)| x == y)
    }
}
