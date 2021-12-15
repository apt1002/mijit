use super::code::{Convention, Action, Switch};

/** Identifies a point where control-flow merges with pre-existing code. */
#[derive(Debug, Copy, Clone)]
pub struct Leaf<'a> {
    pub weight: usize,
    pub after: &'a Convention,
}

impl<'a> PartialEq<Self> for Leaf<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.weight == other.weight &&
        std::ptr::eq(self.after, other.after)
    }
}

impl<'a> Eq for Leaf<'a> {}

/**
 * Represents an [extended basic block], i.e. a tree-like control-flow graph.
 * This is the unit of optimization.
 *
 * [extended basic block]: https://en.wikipedia.org/wiki/Extended_basic_block
 */
#[derive(Debug, Clone)]
pub struct EBB<'a> {
    pub before: Convention,
    pub actions: Vec<Action>,
    pub ending: Ending<'a>,
}

#[derive(Debug, Clone)]
pub enum Ending<'a> {
    /** Control-flow merges with pre-existing code. */
    Leaf(Leaf<'a>),
    /** Control-flow diverges. */
    Switch(Switch<EBB<'a>>),
}

impl<'a> From<Leaf<'a>> for Ending<'a> {
    fn from(v: Leaf<'a>) -> Self {
        Ending::Leaf(v)
    }
}

impl<'a> From<Switch<EBB<'a>>> for Ending<'a> {
    fn from(v: Switch<EBB<'a>>) -> Self {
        Ending::Switch(v)
    }
}
