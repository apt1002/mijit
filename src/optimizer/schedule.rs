use std::fmt::{self, Debug, Formatter};
use std::iter::{Iterator};

use crate::util::{ArrayMap, AsUsize, CommaSeparated};
use super::{Dataflow, Node, Out};

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
    firsts: ArrayMap<Out, Option<Use>>,
    nexts: Vec<Option<Use>>, // Indexed by `Use`.
}

impl<'a> Schedule<'a> {
    /**
     * - dataflow - The [`Dataflow`] used to look up information about [`Node`]s.
     * - nodes - The live [`Node`]s in the order we want to process them.
     * - exit_node - The [`Node`] representing the [`Convention`] on exit.
     *
     * [`Convention`]: super::Convention
     */
    pub fn new(dataflow: &'a Dataflow, nodes: &[Node], exit_node: Node) -> Self {
        let mut schedule = Schedule {
            dataflow: dataflow,
            nodes: Vec::with_capacity(nodes.len()),
            firsts: dataflow.out_map(),
            nexts: Vec::new(),
        };
        for &in_ in schedule.dataflow.ins(exit_node).iter().rev() {
            schedule.push(in_);
        }
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
        self.firsts[out] = Use::new(self.nexts.len());
        self.nexts.push(next);
    }

    /**
     * Pop the next `Use`, asserting that it is the first `Use` of `out`.
     */
    fn pop(&mut self, out: Out) {
        let next = self.nexts.pop().expect("Popped from an empty Schedule");
        assert_eq!(self.firsts[out], Use::new(self.nexts.len()));
        self.firsts[out] = next;
    }

    pub fn first_use(&self, out: Out) -> Option<Use> {
        self.firsts[out]
    }

    pub fn next_use(&self, use_: Use) -> Option<Use> {
        self.nexts[use_.as_usize()]
    }
}

impl<'a> Debug for Schedule<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("Schedule")
            .field("dataflow", self.dataflow)
            .field("nodes", &CommaSeparated(|| &self.nodes))
            .finish()
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
    use super::super::{Op};

    fn all_uses(schedule: &Schedule, out: Out) -> Vec<usize> {
        let mut ret = Vec::new();
        if let Some(mut use_) = schedule.first_use(out) {
            ret.push(use_.as_usize());
            while let Some(next) = schedule.next_use(use_) {
                use_ = next;
                ret.push(use_.as_usize());
            }
        }
        ret
    }

    #[test]
    /** Test that Schedule keeps track of the uses of `Out`s. */
    pub fn test() {
        let mut d = Dataflow::new(2);
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
        let exit_node = d.add_node(Op::Convention, &[], &[out4], 0);
        let mut schedule = Schedule::new(&d, &[node1, node2, node3], exit_node);
        assert_eq!(all_uses(&schedule, out0), [6, 4]);
        assert_eq!(all_uses(&schedule, out1), [5]);
        assert_eq!(schedule.next(), Some(node1));
        assert_eq!(all_uses(&schedule, out0), [4]);
        assert_eq!(all_uses(&schedule, out1), []);
        assert_eq!(all_uses(&schedule, out2), [3, 2]);
        assert_eq!(schedule.next(), Some(node2));
        assert_eq!(all_uses(&schedule, out0), []);
        assert_eq!(all_uses(&schedule, out2), [2]);
        assert_eq!(all_uses(&schedule, out3), [1]);
        assert_eq!(schedule.next(), Some(node3));
        assert_eq!(all_uses(&schedule, out2), []);
        assert_eq!(all_uses(&schedule, out3), []);
        assert_eq!(all_uses(&schedule, out4), [0]);
        assert_eq!(schedule.next(), None);
    }
}
