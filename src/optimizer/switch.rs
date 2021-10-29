use super::{Node, Leaf};

/** Represents a control-flow tree. */
pub enum CFT {
    Merge {
        /** The exit [`Node`] of the dataflow graph for this path. */
        exit: Node,
        /** Where to merge into the existing compiled code. */
        leaf: Leaf,
    },
    Switch {
        /** The [`Op::Guard`] [`Node`] for this `Switch`. */
        guard: Node,
        /** The index of the most probable case, or `usize::MAX`. */
        hot_index: usize,
        /** The `CFT`s of the numbered cases. */
        cases: Box<[CFT]>,
        /** The `CFT` of the default case. */
        default_: Box<CFT>,
    },
}
