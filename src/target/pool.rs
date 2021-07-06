use std::num::{Wrapping};
use std::ops::{Index, IndexMut};
use std::fmt::{self, Debug};

use super::code::{Global};

/** Names a profiling counter. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Counter(usize);

//-----------------------------------------------------------------------------

/** An untyped 64-bit value. */
#[repr(C)]
#[derive(Copy, Clone, Eq)]
pub union Word {
    pub u: u64,
    pub s: i64,
    pub w: Wrapping<u64>,
    pub p: *const (),
    pub mp: *mut (),
}

impl Default for Word {
    fn default() -> Self { Word {u: 0} }
}

impl Debug for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Word")
            .field("u", &format!("{:#x}", unsafe {self.u}))
            .finish()
    }
}

impl PartialEq for Word {
    fn eq(&self, other: &Self) -> bool {
        unsafe {self.u == other.u}
    }
}

//-----------------------------------------------------------------------------

/**
 * A contiguous array of 64-bit words, rewriteable at runtime by the compiled
 * code, providing storage to a virtual machine instance.
 *
 * A pool contains [`Global`]s and profiling counters.
 */
pub struct Pool {
    /** The number of [`Global`]s used by the [`code::Machine`]. */
    num_globals: usize,
    /** The words. */
    pool: Vec<Word>,
}

impl Pool {
    /** Allocate a new `Pool`, initially with no [`Counter`]s. */
    pub fn new(num_globals: usize) -> Self {
        let pool = vec![Word::default(); num_globals];
        Pool {num_globals, pool}
    }

    /** Allocate a profiling counter, initialized to `0`. */
    pub fn new_counter(&mut self) -> Counter {
        let ret = Counter(self.pool.len() - self.index_of_counter(Counter(0)));
        self.pool.push(Word {w: Wrapping(0)});
        ret
    }

    /**
     * The number of [`Global`]s that persist when Mijit is not running.
     * This is the value passed to [`Target::lowerer()`].
     */
    pub fn num_globals(&self) -> usize { self.num_globals }

    /** The position in the pool of the given [`Global`]. */
    pub fn index_of_global(&self, global: Global) -> usize {
        assert!(global.0 < self.num_globals);
        global.0
    }

    /** The position in the pool of the given [`Counter`]. */
    pub fn index_of_counter(&self, counter: Counter) -> usize {
        self.num_globals + counter.0
    }
}

impl AsRef<[Word]> for Pool {
    fn as_ref(&self) -> &[Word] { self.pool.as_ref() }
}

impl AsMut<[Word]> for Pool {
    fn as_mut(&mut self) -> &mut [Word] { self.pool.as_mut() }
}

impl Index<usize> for Pool {
    type Output = Word;
    fn index(&self, index: usize) -> &Self::Output { &self.pool[index] }
}

impl IndexMut<usize> for Pool {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { &mut self.pool[index] }
}

impl Index<Global> for Pool {
    type Output = Word;

    fn index(&self, g: Global) -> &Self::Output {
        let i = self.index_of_global(g);
        &self[i]
    }
}

impl IndexMut<Global> for Pool {
    fn index_mut(&mut self, g: Global) -> &mut Self::Output {
        let i = self.index_of_global(g);
        &mut self[i]
    }
}

impl Index<Counter> for Pool {
    type Output = Wrapping<u64>;

    fn index(&self, c: Counter) -> &Self::Output {
        let i = self.index_of_counter(c);
        unsafe { &self[i].w }
    }
}

impl IndexMut<Counter> for Pool {
    fn index_mut(&mut self, c: Counter) -> &mut Self::Output {
        let i = self.index_of_counter(c);
        unsafe { &mut self[i].w }
    }
}