use super::code::{Convention, Action, Switch};

/**
 * Look up information about a control-flow merge point.
 */
pub trait LookupLeaf<L: Clone> {
    /** Return the convention in effect at `leaf`. */
    fn after(&self, leaf: &L) -> &Convention;
    /** Return the estimated relative frequency of `leaf`. */
    fn weight(&self, leaf: &L) -> usize;
}

/**
 * Represents an [extended basic block], i.e. a tree-like control-flow graph.
 * This is the unit of optimization.
 *
 * `L` identifies a point where control-flow merges with pre-existing code.
 *
 * [extended basic block]: https://en.wikipedia.org/wiki/Extended_basic_block
 */
#[derive(Debug, Clone)]
pub struct EBB<L> {
    pub before: Convention,
    pub actions: Vec<Action>,
    pub ending: Ending<L>,
}

#[derive(Debug, Clone)]
pub enum Ending<L> {
    /** Control-flow merges with pre-existing code. */
    Leaf(L),
    /** Control-flow diverges. */
    Switch(Switch<EBB<L>>),
}
