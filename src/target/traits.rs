use super::{code, Counter, Word, Pool, Patch, Label};
use code::{Variable, Action};

/**
 * Wraps a contiguous block of executable memory, and provides methods for
 * assembling machine code into it. Also wraps a [`Pool`] that can be accessed
 * by the machine code.
 *
 * The low-level memory address of the executable memory will remain constant
 * while the code is executing, but it could change at other times, e.g.
 * because the buffer grows and gets reallocated. Therefore, be wary of
 * absolute memory addresses. `Lower` itself always expresses addresses using
 * [`Label`].
 */
pub trait Lower {
    /** The [`Pool`]. */
    fn pool(&self) -> &Pool;

    /** The [`Pool`]. */
    fn pool_mut(&mut self) -> &mut Pool;

    /**
     * The number of stack-allocated spill [`Slot`]s. Spill `Slot`s are created
     * by [`Push`] instructions and destroyed by [`Pop`] instructions. The
     * number of spill slots at a `jump()` or `Switch` must match the number at
     * its `Label`.
     *
     * Do not mutate the number of spill slots (other that using `Push` and
     * `Pop`) when the current assembly address is reachable.
     *
     * [`Push`]: Action::Push
     * [`Pop`]: Action::Pop
     */
    fn slots_used_mut(&mut self) -> &mut usize;

    /** Returns the current assembly address as a fresh [`Label`]. */
    fn here(&self) -> Label;

    /**
     * Modify the instruction at `patch` so that instead of jumping to
     * `old_target` it jumps to `new_target`.
     *
     * Normally you should prefer `steal()` or `define()`, which call this.
     */
    fn patch(&mut self, patch: Patch, old_target: Option<usize>, new_target: Option<usize>);

    /**
     * Modifies all instructions that jump to `loser` so that they instead
     * jump to `winner`.
     */
    fn steal(&mut self, loser: &mut Label, winner: &mut Label) {
        let loser_target = loser.target();
        for patch in loser.drain() {
            self.patch(patch, loser_target, winner.target());
            winner.push(patch);
        }
    }

    /** Define `label`, which must not previously have been defined. */
    fn define(&mut self, label: &mut Label) {
        assert!(!label.is_defined());
        // Use `steal()` to modify all instructions that jump to `label`.
        let mut new = self.here();
        self.steal(label, &mut new);
        *label = new;
    }

    /** Assemble an unconditional jump to `label`. */
    fn jump(&mut self, label: &mut Label);

    /**
     * Assemble Mijit's function prologue. The function takes one argument:
     *  - The pool pointer.
     */
    fn prologue(&mut self);

    /**
     * Assemble Mijit's function epilogue. The function returns one result:
     *  - The exit code, which is moved from `RESULT`.
     */
    fn epilogue(&mut self);

    /**
     * Assemble code that branches to `eq_label` if the equality test passes.
     */
    fn if_eq(
        &mut self,
        guard: (Variable, u64),
        eq_label: &mut Label,
    );

    /**
     * Assemble code that branches to `ne_label` if the equality test fails.
     */
    fn if_ne(
        &mut self,
        guard: (Variable, u64),
        ne_label: &mut Label,
    );

    /** Assemble code to perform the given `action`. */
    fn action(&mut self, action: Action);

    /** Call `action()` repeatedly. */
    fn actions(&mut self, actions: &[Action]) {
        for &action in actions {
            self.action(action);
        }
    }

    /** Assemble code to increment the given `counter`. */
    fn count(&mut self, counter: Counter);
}

//-----------------------------------------------------------------------------

/** The type of the generated code. */
pub type ExecuteFn = unsafe extern "C" fn(
    /* pool */ *mut Word,
) -> /* result */ Word;

/** Add to [`Lower`] the ability to execute the compiled code. */
pub trait Execute: Sized + Lower {
    /**
     * Make the memory backing `self` executable, pass the code at `label` and
     * the words of the [`Pool`] to `callback`, then make the memory writeable
     * (and not executable) again.
     *
     * `callback` is typically something like
     * `|f, pool| f(pool.as_mut().as_mut_ptr())`.
     *
     * If we can't change the memory permissions, you get an [`Err`] and `self`
     * is gone.
     */
    fn execute<T>(
        self,
        label: &Label,
        callback: impl FnOnce(ExecuteFn, &mut Pool) -> T,
    ) -> std::io::Result<(Self, T)>;
}

//-----------------------------------------------------------------------------

/**
 * Represents a compilation target. Most importantly, this defines the CPU
 * architecture that Mijit will generate code for. It also defines how Mijit
 * will allocate and make executable the memory for the code.
 *
 * A type that implements `Target` is usually a zero-sized struct, but it can
 * contain flags and other configuration data. `Default::default()` recommends
 * the best configuation for the machine Mijit is running on.
 */
pub trait Target: Default {
    type Lowerer: Lower + Execute;

    /** The number of registers available for allocation. */
    const NUM_REGISTERS: usize;

    /**
     * Construct a [`Lowerer`] for this `Target`.
     *  - `pool` - The per-VM pool of memory.
     *  - `code_size` - The amount of memory to allocate for executable code.
     */
    // TODO: Remove `code_size` and make the lowerer auto-extend its buffer.
    fn lowerer(&self, pool: Pool) -> Self::Lowerer;
}
