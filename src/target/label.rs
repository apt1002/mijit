/** Represents the address of an instruction that jumps to a `Label`. */
#[derive(Debug, Copy, Clone)]
pub struct Patch(usize);

impl Patch {
    /** The address is expressed as a byte offset into the compiled code. */
    pub fn new(address: usize) -> Self { Patch(address) }

    pub fn address(&self) -> usize { self.0 }
}

//-----------------------------------------------------------------------------

/**
 * Represents a possibly unknown control-flow target, and accumulates a
 * set of instructions that jump to it. Undefined `Label`s can be resolved
 * using `Lowerer::define()`. The instructions that jump to a `Label`
 * can be redirected to another `Label` using `Lowerer::steal()`.
 *
 * There may be more than one `Label` targeting the same address; each can
 * be [`steal()`]ed separately. Each control-flow instruction targets
 * exactly one `Label`.
 *
 * [`steal()`]: super::Lower::steal
 */
#[derive(Debug)]
pub struct Label {
    target: Option<usize>,
    patches: Vec<Patch>,
}

impl Label {
    /**
     * Constructs an unused `Label`. See also [`here()`]
     *  - target - the low-level target address of the `Label`, if known,
     *    expressed as a byte offset into the compiled code.
     *
     * [here()]: super::Lower::here
     */
    pub fn new(target: Option<usize>) -> Self {
        Label {target, patches: Vec::new()}
    }

    /** Returns the low-level target address of this `Label`, if known. */
    pub fn target(&self) -> Option<usize> { self.target }

    /** Tests whether `label` has a known target address. */
    pub fn is_defined(&self) -> bool {
        self.target().is_some()
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
    fn default() -> Self { Label::new(None) }
}
