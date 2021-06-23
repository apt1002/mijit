use super::{code, Word, Pool, Label};
use code::{Precision, Register, Value, TestOp, UnaryOp, BinaryOp, Action};

/**
 * Wraps a contiguous block of executable memory, and provides methods for
 * assembling machine code into it. Also wraps a [`Pool`] that can be accessed
 * by the machine code.
 *
 * The low-level memory address of the executable memory will remain constant
 * while the code is executing, but it could change at other times, e.g.
 * because the buffer grows and gets reallocated. Therefore, be wary of
 * absolute memory addresses. `Lower` itself always expresses addresses as
 * a byte offset into the code area. [`Label`] provides a higher-level API.
 */
pub trait Lower: Sized {
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

    /** Returns the current assembly address (a byte offset into the code). */
    fn here(&self) -> usize;

    /**
     * Modifies all instructions that jump to `loser` so that they instead
     * jump to `winner`.
     */
    fn steal(&mut self, winner: &mut Label, loser: &mut Label);

    /** Define `label`, which must not previously have been defined. */
    fn define(&mut self, label: &mut Label) {
        assert!(!label.is_defined());
        // Use `steal()` to modify all instructions that jump to `label`.
        let mut new = Label::new();
        super::label::define(&mut new, self.here());
        self.steal(&mut new, label);
        *label = new;
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

/** The type of the generated code. */
pub type ExecuteFn = extern "C" fn(
    /* pool */ *mut Word,
    /* argument */ Word,
) -> /* result */ Word;

/** Add to [`Lower`] the ability to execute the compiled code. */
pub trait Execute: Sized + Lower {
    /**
     * Make the memory backing `self` executable, pass the code at `label` and
     * the words of the [`Pool`] to `callback`, then make the memory writeable
     * (and not executable) again.
     *
     * If we can't change the memory permissions, you get an [`Err`] and `self`
     * is gone. `T` can itself be a [`Result`] if necessary to represent errors
     * returned by `callback`.
     */
    fn execute<T>(
        self,
        label: &Label,
        callback: impl FnOnce(ExecuteFn, &mut Pool) -> T,
    ) -> std::io::Result<(Self, T)>;
}

//-----------------------------------------------------------------------------

pub trait Target {
    type Lowerer: Lower + Execute;

    /** The number of registers available for allocation. */
    const NUM_REGISTERS: usize;

    /**
     * Construct a [`Lowerer`] for this `Target`.
     *  - `pool` - The per-VM pool of memory.
     *  - `code_size` - The amount of memory to allocate for executable code.
     */
    // TODO: Remove `code_size` and make the lowerer auto-extend its buffer.
    fn lowerer(&self, pool: Pool, code_size: usize) -> Self::Lowerer;
}
