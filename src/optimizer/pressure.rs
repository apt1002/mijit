use std::cmp::{Ord};

/**
 * Represents register pressure as a decreasing function of `T`. If the
 * pressure is not a decreasing function, the pressure is increased to fill
 * the "valleys".
 *
 * `T` represents time. `T` can increase forwards or backwards; we therefore
 * use the terminology "larger" and "smaller", not "earlier" or "later".
 */
#[derive(Debug, Clone)]
pub struct Pressure<T: Copy + Ord> {
    /**
     * Element `n` gives the smallest `T` at which `n` `Register`s are in use.
     */
    times: Box<[T]>,
    /** The smallest possible time. */
    smallest_time: T,
}

impl<T: Copy + Ord> Pressure<T> {
    /** Initially, all `Register`s are free from `smallest_time`. */
    pub fn new(num_registers: usize, smallest_time: T) -> Self {
        Pressure {
            times: (0..num_registers).map(|_| smallest_time).collect(),
            smallest_time: smallest_time,
        }
    }

    /** Returns the smallest `T` at which `n` `Register`s are unused. */
    pub fn smallest_time_with_unused_registers(&self, n: usize) -> T {
        if n == 0 {
            self.smallest_time
        } else {
            self.times[self.times.len() - n]
        }
    }

    /**
     * Increments the Register pressure in the interval from (at most) `low`
     * to `high`.
     */
    pub fn allocate_register(&mut self, low: T, mut high: T) {
        for t in self.times.iter_mut() {
            if low >= high { break; }
            if high > *t { std::mem::swap(&mut high, t); }
        }
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pressure() {
        let mut p: Pressure<usize> = Pressure::new(3, 0);
        assert_eq!(*p.times, [0, 0, 0]);
        p.allocate_register(0, 4);
        assert_eq!(*p.times, [4, 0, 0]);
        p.allocate_register(6, 8); // Gap from 4 to 6 is filled.
        assert_eq!(*p.times, [8, 0, 0]);
        p.allocate_register(5, 1); // Denotes an empty interval.
        assert_eq!(*p.times, [8, 0, 0]);
        p.allocate_register(0, 5);
        assert_eq!(*p.times, [8, 5, 0]);
        p.allocate_register(3, 6); // Gap from 0 to 3 is filled.
        assert_eq!(*p.times, [8, 6, 5]);
        p.allocate_register(7, 9); // Gap from 6 to 7 is filled.
        assert_eq!(*p.times, [9, 8, 5]);
        p.allocate_register(2, 4); // Spilled.
        assert_eq!(*p.times, [9, 8, 5]);
        p.allocate_register(3, 6); // Partially spilled.
        assert_eq!(*p.times, [9, 8, 6]);
    }
}
