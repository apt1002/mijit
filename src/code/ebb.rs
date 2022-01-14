use super::{Convention, Action, Switch};

/**
 * Represents an [extended basic block], i.e. a tree-like control-flow graph.
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
