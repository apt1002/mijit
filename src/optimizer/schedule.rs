use std::cmp::{Reverse};
use std::iter::{Iterator};
use std::num::{NonZeroUsize};

use crate::util::{ArrayMap};
use super::{Dataflow, Node, Out};

/**
 * Represents a place where an [`Out`] is used in a [`Schedule`].
 * `u < v` means `u` occurs before `v` in the [`Schedule`].
 */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Use(
    /** The number of times any `Out` is read after this `Use`. */ 
    Reverse<usize>,
);

/**
 * Represent a list of places where an [`Out`] is used.
 * The union of all the `UseList`s for a [`Schedule`] is the numbers from `0`
 * to `n-1` where `n` is the total number of times any `Out` is read during the
 * `Schedule`.
 */
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq)]
struct UseList(
    /** 1 + the first `Use`, if any. */
    Option<NonZeroUsize>
);

impl UseList {
    pub fn new(next: usize) -> Self {
        UseList(NonZeroUsize::new(next + 1))
    }

    pub fn first(self) -> Option<Use> {
        self.0.map(|n| Use(Reverse(n.get() - 1)))
    }
}

/**
 * An approximation of the order in which we'd like to execute some [`Node`]s.
 *
 * `Schedule` implements [`Iterator`] and yields the `Node`s in order.
 *
 * Schedule also maintains a data structure to keep track of where [`Out`]s
 * are used. At any point, you can query the `Schedule` and find out all future
 * [`Use`]s of an `Out`.
 */
pub struct Schedule<'a> {
    pub dataflow: &'a Dataflow,
    nodes: Vec<Node>,
    firsts: ArrayMap<Out, UseList>,
    nexts: Vec<UseList>,
}

impl<'a> Schedule<'a> {
    pub fn new(dataflow: &'a Dataflow, nodes: &[Node]) -> Self {
        let mut schedule = Schedule {
            dataflow: dataflow,
            nodes: Vec::with_capacity(nodes.len()),
            firsts: dataflow.out_map(),
            nexts: Vec::new(),
        };
        for &node in nodes.iter().rev() {
            schedule.nodes.push(node);
            for &in_ in schedule.dataflow.ins(node).iter().rev() {
                schedule.push(in_);
            }
        }
        schedule
    }

    /** Push the next `Use` onto the `UseList` for `out`. */
    fn push(&mut self, out: Out) {
        let next = self.firsts[out];
        self.firsts[out] = UseList::new(self.nexts.len());
        self.nexts.push(next);
    }

    /**
     * Pop the next `Use`, asserting that it is the first `Use` of `out`.
     */
    fn pop(&mut self, out: Out) {
        let next = self.nexts.pop().expect("Popped from an empty Schedule");
        assert_eq!(self.firsts[out], UseList::new(self.nexts.len()));
        self.firsts[out] = next;
    }

    pub fn first_use(&self, out: Out) -> Option<Use> {
        self.firsts[out].first()
    }
}

impl<'a> Iterator for Schedule<'a> {
    type Item = Node;

    fn next(&mut self) -> Option<Self::Item> {
        self.nodes.pop().map(|node| {
            for &in_ in self.dataflow.ins(node) {
                self.pop(in_);
            }
            node
        })
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{code, Op};
    use code::{Slot};

    #[test]
    /** Test that Schedule keeps track of the uses of `Out`s. */
    pub fn test() {
        let mut d = Dataflow::new(vec![Slot(0).into(), Slot(1).into()]);
        let mut it = d.outs(d.entry_node());
        let out0 = it.next().unwrap();
        let out1 = it.next().unwrap();
        let node1 = d.add_node(Op::Convention, &[], &[out0, out1], 1);
        let mut it = d.outs(node1);
        let out2 = it.next().unwrap();
        let node2 = d.add_node(Op::Convention, &[], &[out0, out2], 1);
        let mut it = d.outs(node2);
        let out3 = it.next().unwrap();
        let node3 = d.add_node(Op::Convention, &[], &[out2, out3], 1);
        let mut it = d.outs(node3);
        let out4 = it.next().unwrap();
        let mut schedule = Schedule::new(&d, &[node1, node2, node3]);
        assert_eq!(schedule.first_use(out0), Some(Use(Reverse(5))));
        assert_eq!(schedule.first_use(out1), Some(Use(Reverse(4))));
        assert_eq!(schedule.next(), Some(node1));
        assert_eq!(schedule.first_use(out0), Some(Use(Reverse(3))));
        assert_eq!(schedule.first_use(out1), None);
        assert_eq!(schedule.first_use(out2), Some(Use(Reverse(2))));
        assert_eq!(schedule.next(), Some(node2));
        assert_eq!(schedule.first_use(out0), None);
        assert_eq!(schedule.first_use(out2), Some(Use(Reverse(1))));
        assert_eq!(schedule.first_use(out3), Some(Use(Reverse(0))));
        assert_eq!(schedule.next(), Some(node3));
        assert_eq!(schedule.first_use(out2), None);
        assert_eq!(schedule.first_use(out3), None);
        assert_eq!(schedule.first_use(out4), None);
    }
}
