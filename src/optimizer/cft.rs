use super::{Node, Leaf};

//-----------------------------------------------------------------------------

/**
 * The cold branches from a [`Op::Guard`], along with the information needed
 * to combine them with the hot branch to reconstruct the whole `Switch`.
 *
 * This is used in the return type of [`CFT::hot_path()`].
 */
pub struct Cold<T> {
    /** The [`Op::Guard`] that separates these `Colds` from the hot path. */
    pub guard: Node,
    /** The index of the most probable case, or `usize::MAX`. */
    pub hot_index: usize,
    /** A `T` for each cold branch (omitting the hot branch). */
    pub colds: Box<[T]>,
}

impl<T> Cold<T> {
    /** Separates the hot and cold paths of a [`CFT::Switch`]. */
    pub fn new(
        guard: Node,
        hot_index: usize,
        mut cases: Vec<T>,
        default_: T,
    ) -> (T, Self) {
        let hot = if hot_index == usize::MAX {
            default_
        } else {
            let hot = cases.remove(hot_index);
            cases.push(default_);
            hot
        };
        let colds = cases.into_boxed_slice();
        (hot, Cold {guard, hot_index, colds})
    }
}

//-----------------------------------------------------------------------------

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

impl CFT {
    /**
     * Follows the hot path through `cft`.
     * Returns the [`Colds`]es and the exit [`Node`].
     */
    pub fn hot_path(&self) -> (Vec<Cold<&Self>>, Node) {
        let mut cft = self;
        let mut colds = Vec::new();
        loop {
            match cft {
                &CFT::Merge {exit, ..} => {
                    return (colds, exit);
                },
                &CFT::Switch {guard, hot_index, ref cases, ref default_} => {
                    let cases: Vec<&Self> = cases.iter().collect();
                    let (hot, cold) = Cold::new(guard, hot_index, cases, default_);
                    cft = hot;
                    colds.push(cold);
                },
            }
        }
    }
}
