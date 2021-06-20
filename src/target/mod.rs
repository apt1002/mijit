use std::num::{Wrapping};
use std::ops::{Index, IndexMut};
use std::fmt::{self, Debug};

use super::{code};
use code::{Precision, Global, Register, Value, TestOp, UnaryOp, BinaryOp, Action};

pub mod x86_64;

/**
 * The [`Register`] which holds the state index on entry and exit from Mijit.
 */
// TODO: Somehow hide the state index from this module, and delete this.
pub const STATE_INDEX: Register = code::REGISTERS[0];

//-----------------------------------------------------------------------------

/** Represents the address of an instruction that jumps to a `Label`. */
#[derive(Debug, Copy, Clone)]
pub struct Patch(usize);

/**
 * Represents a possibly unknown control-flow target, and accumulates a
 * set of instructions that jump to it. The target of a `Label` can be
 * changed by calling [`patch()`].
 *
 * There may be more than one `Label` targeting the same address; each can
 * be [`patch()`]ed separately. Each control-flow instruction targets
 * exactly one `Label`.
 *
 * [`patch()`]: Lowerer::patch
 */
#[derive(Debug)]
pub struct Label {
    target: Option<usize>,
    patches: Vec<Patch>,
}

impl Label {
    /** Constructs an unused `Label` with an unknown target address. */
    pub fn new() -> Self {
        Label {target: None, patches: Vec::new()}
    }

    /** Tests whether `label` has a known target address. */
    pub fn is_defined(&self) -> bool {
        self.target.is_some()
    }

    /** Appends `patch` to the list of instructions that jump to `self`. */
    pub fn push(&mut self, patch: Patch) {
        self.patches.push(patch);
    }

    /** Returns and forgets all the instructions that jump to `self`. */
    pub fn drain(&mut self) -> impl Iterator<Item=Patch> + '_ {
        self.patches.drain(..)
    }
}

impl Default for Label {
    fn default() -> Self { Label::new() }
}

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

/**
 * A contiguous array of 64-bit words, rewriteable at runtime by the compiled
 * code, providing storage to a virtual machine instance.
 *
 * A pool contains constant values defined by the [`Target`], [`Global`]s, and
 * profiling counters.
 */
pub struct Pool {
    /** The number of constants defined by the [`Target`]. */
    num_constants: usize,
    /** The number of [`Global`]s used by the [`code::Machine`]. */
    num_globals: usize,
    /** The words. */
    pool: Vec<Word>,
}

impl Pool {
    /** Allocate a new `Pool`. */
    pub fn new(target: &impl Target, num_globals: usize) -> Self {
        let constants = target.constants();
        let num_constants = constants.len();
        let mut pool = vec![Word::default(); num_constants + num_globals];
        pool[..num_constants].copy_from_slice(constants);
        Pool {num_constants, num_globals, pool}
    }

    /** The number of constants needed by the [`Target`]. */
    pub fn num_constants(&self) -> usize { self.num_constants }

    /**
     * The number of [`Global`]s that persist when Mijit is not running.
     * This is the value passed to [`Target::lowerer()`].
     */
    pub fn num_globals(&self) -> usize { self.num_globals }

    /** Provides access to the words. */
    pub fn as_mut_ptr(&mut self) -> *mut Word { self.pool.as_mut_ptr() }

    /** The position in the pool of the constant with the given index. */
    pub fn index_of_constant(&self, index: usize) -> usize {
        assert!(index < self.num_constants);
        index
    }

    /** The position in the pool of the given [`Global`]. */
    pub fn index_of_global(&self, global: Global) -> usize {
        assert!(global.0 < self.num_globals);
        self.num_constants + global.0
    }

    /** The position in the pool of the counter with the given index. */
    pub fn index_of_counter(&self, index: usize) -> usize {
        self.num_constants + self.num_globals + index
    }
}

impl Index<usize> for Pool {
    type Output = Word;
    fn index(&self, index: usize) -> &Self::Output { &self.pool[index] }
}

impl std::ops::IndexMut<usize> for Pool {
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

//-----------------------------------------------------------------------------

/**
 * Wraps a contiguous block of executable memory, and provides methods for
 * assembling machine code into it.
 *
 * The low-level memory address of the executable memory will remain constant
 * while the code is executing, but it could change at other times, e.g.
 * because the buffer grows and gets reallocated. Therefore, be wary of absolute
 * memory addresses. Lowerer itself never uses them. For code addresses,
 * use [`Label`].
 */
pub trait Lowerer: Sized {
    /** The [`Pool`]. */
    fn pool(&self) -> &Pool;

    /** The [`Pool`]. */
    fn pool_mut(&mut self) -> &mut Pool;

    /**
     * The number of stack-allocated spill [`Slot`]s. Spill `Slot`s are created
     * by [`Push`] instructions and destroyed by [`Pop`] instructions. The
     * number of spill slots at a `jump()` or `TestOp` must match the number at
     * its `Label`.
     *
     * Do not mutate the number of spill slots (other that using `Push` and
     * `Pop`) when the current assembly address is reachable.
     *
     * [`Push`]: Action::Push
     * [`Pop`]: Action::Pop
     */
    fn slots_used(&mut self) -> &mut usize;

    /** Returns the current assembly address. */
    fn here(&self) -> usize;

    /**
     * Modifies all instructions that jump to `loser` so that they instead
     * jump to `winner`.
     */
    fn steal(&mut self, winner: &mut Label, loser: &mut Label);

    /**
     * Sets the target of `label` to the current assembly address, and writes
     * it into all the instructions that jump to `label`. If `label` has not
     * been defined before, prefer `define(&mut Label)`, which calls this.
     *
     * It is permitted to patch a Label more than once. For example, you could
     * set the target to one bit of code, execute it for a while, then set the
     * target to a different bit of code, and execute that.
     *
     * Returns the old target of this Label as a fresh (unused) Label. This is
     * useful if you want to assemble some new code that jumps to the old code.
     */
    fn patch(&mut self, label: &mut Label) -> Label {
        let mut old = Label::new();
        old.target = Some(self.here());
        std::mem::swap(label, &mut old);
        self.steal(label, &mut old);
        old
    }

    /** Define `label`, which must not previously have been defined. */
    fn define(&mut self, label: &mut Label) {
        assert!(!label.is_defined());
        let _unused_and_undefined = self.patch(label);
    }

    /** Assemble an unconditional jump to `label`. */
    fn jump(&mut self, label: &mut Label);

    /**
     * Assemble Mijit's function prologue. The function takes two arguments:
     *  - The pool pointer.
     *  - The state index, which is moved to `STATE_INDEX`.
     */
    fn lower_prologue(&mut self);

    /**
     * Assemble Mijit's function epilogue. The function returns one result:
     *  - The state index, which is moved from `STATE_INDEX`.
     */
    fn lower_epilogue(&mut self);

    /**
     * Assemble code that branches to `false_label` if `test_op` is false.
     */
    fn lower_test_op(
        &mut self,
        guard: (TestOp, Precision),
        false_label: &mut Label,
    );

    /**
     * Assemble code to perform the given `unary_op`.
     */
    fn lower_unary_op(
        &mut self,
        unary_op: UnaryOp,
        prec: Precision,
        dest: Register,
        src: Value,
    );

    /**
     * Assemble code to perform the given `binary_op`.
     */
    fn lower_binary_op(
        &mut self,
        binary_op: BinaryOp,
        prec: Precision,
        dest: Register,
        src1: Value,
        src2: Value,
    );

    /**
     * Assemble code to perform the given `action`.
     */
    fn lower_action(&mut self, action: Action);
}

//-----------------------------------------------------------------------------

pub trait Target {
    type Lowerer: Lowerer;

    /** The number of registers available for allocation. */
    const NUM_REGISTERS: usize;

    /** Returns some constants to copy into the per-VM pool of memory. */
    fn constants(&self) -> &[Word];

    /**
     * Construct a [`Lowerer`] for this `Target`.
     *  - `pool` - The per-VM pool of memory.
     *  - `code_size` - The amount of memory to allocate for executable code.
     */
    // TODO: Remove `code_size` and make the lowerer auto-extend its buffer.
    fn lowerer(&self, pool: Pool, code_size: usize) -> Self::Lowerer;

    /**
     * Make the memory backing `lowerer` executable, pass it to `callback`,
     * then make it writeable again.
     *
     * If we can't change the buffer permissions, you get an [`Err`] and the
     * `lowerer` is gone. `T` can itself be a [`Result`] if necessary to
     * represent errors returned by `callback`.
     */
    fn execute<T>(
        &self,
        lowerer: Self::Lowerer,
        callback: impl FnOnce(&[u8]) -> T,
    ) -> std::io::Result<(Self::Lowerer, T)>;
}

/** A [`Target`] that generates code which can be executed. */
pub fn native() -> impl Target {
    x86_64::Target
}
