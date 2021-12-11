use super::code::{Convention, Action, Switch};

/**
 * Identifies a point where control-flow leaves an [`EBB`] and merges with
 * pre-existing code.
 */
#[derive(Debug, Copy, Clone)]
pub struct Leaf;

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
    pub actions: Vec<Action>,
    pub switch: Option<Switch<EBB>>,
}
