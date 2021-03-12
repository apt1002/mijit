use std::marker::{PhantomData};

use crate::util::{ArrayMap};
use super::{Dataflow, Out};

/**
 * A partition of the integers from `0` to `n-1`, with one part for each
 * [`Out`] of a [`Dataflow`].
 *
 * The intended use of this data structure is that the numbers from `0` to
 * `n-1` represent all the values read by a program, in reverse order. The
 * part associated with an `Out` is the list of usages of that `Out`.
 */
pub struct Usage<'a> {
    parts: ArrayMap<Out, Part>,
    nexts: Vec<usize>,
    dataflow: PhantomData<&'a Dataflow>,
}

impl<'a> Usage<'a> {
    pub fn new(dataflow: &'a Dataflow) -> Self {
        Usage {
            parts: dataflow.out_map(),
            nexts: Vec::new(),
            dataflow: PhantomData,
        }
    }

    /** Returns the total size of all partitions. */
    pub fn len(&self) -> usize {
        self.nexts.len()
    }

    /** Add the next integer to this partition, putting it in part `out`. */
    pub fn push(&mut self, out: Out) {
        let next = self.parts[out].largest;
        self.parts[out].largest = self.nexts.len();
        self.nexts.push(next)
    }

    /**
     * Remove the largest integer from this partition, asserting that it is
     * in part `out`.
     */
    pub fn pop(&mut self, out: Out) {
        let next = self.nexts.pop().expect("Popped from an empty partition");
        assert_eq!(self.parts[out].largest, self.nexts.len());
        self.parts[out].largest = next;
    }
}

/** The information stored about each [`Out`]. */
#[derive(Debug, Clone, Default)]
pub struct Part {
    /** The smallest integer in the part. */
    smallest: usize,
    /** The largest integer in the part. */
    largest: usize,
    /** The size of the part. */
    count: usize,
}
