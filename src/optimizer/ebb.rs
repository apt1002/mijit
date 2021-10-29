use super::code::{Convention, Action, Switch};

/**
 * Identifies a point where control-flow leaves an [`EBB`] and merges with
 * pre-existing code.
 */
#[derive(Debug, Copy, Clone)]
pub struct Leaf;

/**
 * Represents a [basic block], i.e. some straight-line code followed by a
 * [`Switch`].
 *
 * [basic block]: https://en.wikipedia.org/wiki/Basic_block
 */
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub actions: Vec<Action>,
    pub switch: Switch<EBB>,
}

/**
 * Represents an [extended basic block], i.e. a tree-like control-flow graph,
 * comprised of [`BasicBlock`]s. This is the unit of optimization.
 *
 * [extended basic block]: https://en.wikipedia.org/wiki/Extended_basic_block
 */
#[derive(Debug, Clone)]
pub struct EBB {
    pub leaf: Leaf,
    pub convention: Convention,
    pub weight: usize,
    pub block: Option<Box<BasicBlock>>,
}
