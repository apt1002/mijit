use std::collections::{HashMap};
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash};

use crate::util::{CommaSeparated};

array_index! {
    /**
     * Represents a place where an [`Out`] is used in a [`Schedule`].
     * `u < v` means `u` occurs after `v` in the [`Schedule`].
     */
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Use(
        /** The number of times any `Out` is read after this `Use`. */ 
        std::num::NonZeroUsize
    ) {
        debug_name: "Use",
        UInt: usize,
    }
}

//-----------------------------------------------------------------------------

/**
 * Tracks when things ("values") are used by other things ("instructions").
 * `I` is the type of instructions and `V` is the type of values.
 *
 * A `Usage` behaves like a stack. It is filled by pushing instructions in
 * reverse order, so that `pop()` will then return them in execution order.
 *
 * `first()` allows you to determine which of two values is used first in
 * execution order.
 */
pub struct Usage<I: Debug, V: Debug + Clone + Hash + Eq> {
    /**
     * The instructions in the order they were pushed, each with the length of
     * `nexts` at the time it was pushed.
     */
    instructions: Vec<(I, usize)>,
    /** For each value, its most recently pushed [`Use`]. */
    heads: HashMap<V, Use>,
    /** For each [`Use`], the value used and its next `Use` if any. */
    nexts: Vec<(V, Option<Use>)>,
}

impl<I: Debug, V: Debug + Clone + Hash + Eq> Usage<I, V> {
    /**
     * Returns the most recently pushed use of `value`, if any, i.e. the next
     * use of `value` in execution order.
     *
     * The ordering is such that `u > v` iff `u` was more recently pushed, i.e.
     * if `u` will be used first in execution order.
     */
    pub fn first(&self, value: V) -> Option<impl Ord> {
        self.heads.get(&value).cloned()
    }

    /** Push `instruction` which uses `values`. */
    pub fn push(&mut self, instruction: I, values: impl IntoIterator<Item=V>) {
        self.instructions.push((instruction, self.nexts.len()));
        for v in values {
            let next = self.heads.insert(v.clone(), Use::new(self.nexts.len()).expect("Overflow"));
            self.nexts.push((v, next));
        }
    }

    /** Pop an instruction. */
    pub fn pop<'a>(&'a mut self) -> Option<I> {
        self.instructions.pop().map(|(instruction, length)| {
            let to_remove = length..self.nexts.len();
            for i in to_remove.clone().rev() {
                let (ref v, next) = self.nexts[i];
                let head = if let Some(mut next) = next {
                    std::mem::swap(&mut next, self.heads.get_mut(v).expect("Missing head"));
                    next
                } else {
                    self.heads.remove(v).expect("Missing head")
                };
                assert_eq!(head, Use::new(i).expect("Overflow"));
            }
            self.nexts.drain(to_remove);
            instruction
        })
    }
}

impl<I: Debug, V: Debug + Clone + Hash + Eq> Default for Usage<I, V> {
    fn default() -> Self {
        Usage {instructions: Vec::new(), heads: HashMap::new(), nexts: Vec::new()}
    }
}

impl<I: Debug, V: Debug + Clone + Hash + Eq> Debug for Usage<I, V> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        f.write_str("Usage ")?;
        let mut dm = f.debug_map();
        let mut next = self.nexts.len();
        for &(ref instruction, length) in self.instructions.iter().rev() {
            dm.entry(instruction, &CommaSeparated(|| &self.nexts[length..next]));
            next = length;
        }
        dm.finish()
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{AsUsize};

    // Returns usizes rather than Uses to simplify the callers.
    fn all_uses<I: Debug, V: Debug + Clone + Hash + Eq>(
        usage: &Usage<I, V>,
        value: &V,
    ) -> Vec<usize> {
        let mut ret = Vec::new();
        let mut head: Option<Use> = usage.heads.get(value).cloned();
        while let Some(next) = head {
            ret.push(next.as_usize());
            head = usage.nexts[next.as_usize()].1;
        }
        ret
    }

    fn pop_with_values<I: Debug, V: Debug + Clone + Hash + Eq>(
        usage: &mut Usage<I, V>,
    ) -> (I, Vec<V>) {
        let &(_, length) = usage.instructions.last().unwrap();
        let slice = &usage.nexts[length..usage.nexts.len()];
        let top_values = slice.iter().map(|(v, _)| v.clone()).collect();
        (usage.pop().unwrap(), top_values)
    }

    #[test]
    /** Test that Schedule keeps track of the uses of `Out`s. */
    pub fn test() {
        let mut usage: Usage<char, usize> = Default::default();
        usage.push('D', vec![4]);
        usage.push('C', vec![2, 3]);
        usage.push('B', vec![0, 2]);
        usage.push('A', vec![0, 1]);
        // Test instruction 'A'.
        assert_eq!(all_uses(&usage, &0), vec![5, 3]);
        assert_eq!(all_uses(&usage, &1), vec![6]);
        let (i, vs) = pop_with_values(&mut usage);
        assert_eq!(i, 'A');
        assert_eq!(vs, vec![0, 1]);
        // Test instruction 'B'.
        assert_eq!(all_uses(&usage, &0), vec![3]);
        assert_eq!(all_uses(&usage, &1), vec![]);
        assert_eq!(all_uses(&usage, &2), vec![4, 1]);
        let (i, vs) = pop_with_values(&mut usage);
        assert_eq!(i, 'B');
        assert_eq!(vs, vec![0, 2]);
        // Test instruction 'C'.
        assert_eq!(all_uses(&usage, &0), vec![]);
        assert_eq!(all_uses(&usage, &2), vec![1]);
        assert_eq!(all_uses(&usage, &3), vec![2]);
        let (i, vs) = pop_with_values(&mut usage);
        assert_eq!(i, 'C');
        assert_eq!(vs, vec![2, 3]);
        // Test instruction 'D'.
        assert_eq!(all_uses(&usage, &2), vec![]);
        assert_eq!(all_uses(&usage, &3), vec![]);
        assert_eq!(all_uses(&usage, &4), vec![0]);
        let (i, vs) = pop_with_values(&mut usage);
        assert_eq!(i, 'D');
        assert_eq!(vs, vec![4]);
        // Test final state.
        assert_eq!(all_uses(&usage, &3), vec![]);
        assert_eq!(all_uses(&usage, &4), vec![]);
        assert!(usage.pop().is_none());
    }
}
