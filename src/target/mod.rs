use std::fmt::{Debug};

use super::{code};
use code::{Precision, Register, Value, TestOp, UnaryOp, BinaryOp, Action};

pub mod x86_64;

/**
 * The [`Register`] which holds the state index on entry and exit from Mijit.
 */
// TODO: Somehow hide the state index from this module, and delete this.
pub const STATE_INDEX: Register = code::REGISTERS[0];

//-----------------------------------------------------------------------------

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
    patches: Vec<usize>,
}

impl Label {
    /** Constructs an unused Label. */
    pub fn new(target: Option<usize>) -> Self {
        Label {target: target, patches: Vec::new()}
    }

    /** Returns the current address of this Label. */
    pub fn target(&self) -> Option<usize> {
        self.target
    }

    /**
     * Sets the target of this `Label` to `new_target`, and applies `callback`
     * to all the instructions that jump to this `Label`.
     *
     * Returns the old target of this `Label` as a fresh `Label`. This is
     * useful if you want to assemble some new code that jumps to the old code.
     *
     * - `callback` - a function that patches a jump or call instruction. It
     * receives three arguments:
     *   - the offset of the instruction to patch,
     *   - `new_target`,
     *   - the current target of the instruction.
     */
    pub fn patch(&mut self, new_target: usize, mut callback: impl FnMut(usize, Option<usize>, Option<usize>))
    -> Self {
        let old = Label::new(self.target);
        self.target = Some(new_target);
        for &mut patch in &mut self.patches {
            callback(patch, self.target, old.target);
        }
        old
    }

    /** Add `patch` to the list of instructions that jump to this label. */
    pub fn push(&mut self, patch: usize) {
        self.patches.push(patch);
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
    /** Constructs an unused `Label` with an unknown target address. */
    fn new_label(&self) -> Label;

    /** Tests whether `label` has a known target address. */
    fn is_defined(&self, label: &Label) -> bool;

    /**
     * Sets the target of `label` to the current assembly address, and writes
     * it into all the instructions that jump to `label`. In simple cases,
     * prefer `define(&mut Label)`, which calls this.
     *
     * It is permitted to patch a Label more than once. For example, you could
     * set the target to one bit of code, execute it for a while, then set the
     * target to a different bit of code, and execute that.
     *
     * Returns the old target of this Label as a fresh (unused) Label. This is
     * useful if you want to assemble some new code that jumps to the old code.
     */
    fn patch(&mut self, label: &mut Label) -> Label;

    /** Define `label`, which must not previously have been defined. */
    fn define(&mut self, label: &mut Label) {
        let old = self.patch(label);
        assert!(!self.is_defined(&old));
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

    /** Construct a [`Lowerer`] for this `Target`. */
    fn lowerer(&self, capacity: usize) -> Self::Lowerer;

    /**
     * Make the memory backing `lowerer` executable, pass it to `callback`,
     * then make it writeable again.
     *
     * If we can't change the buffer permissions, you get an [`Err`] and the
     * `lowerer` is gone. `T` can itself be a [`Result`] if necessary to
     * represent errors returned by `callback`
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