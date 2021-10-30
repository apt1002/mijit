use super::{Node, Leaf};

//-----------------------------------------------------------------------------

/**
 * The hot and cold branches from a [`Op::Guard`].
 *
 * This is the return type of [`CFT::hot_path()`].
 */
pub struct HotCold<'a> {
    pub guard: Node,
    pub hot: &'a CFT,
    pub colds: Vec<&'a CFT>,
}

impl<'a> HotCold<'a> {
    /** Separates the hot and cold paths of a [`CFT::Switch`]. */
    pub fn new(guard: Node, hot_index: usize, cases: &'a [CFT], default_: &'a CFT) -> Self {
        let mut hot = default_;
        let mut colds = Vec::new();
        for (i, case) in cases.iter().enumerate() {
            if i == hot_index {
                hot = case;
            } else {
                colds.push(case);
            }
        }
        if hot_index != usize::MAX {
            colds.push(default_);
        }
        HotCold {guard, hot, colds}
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
     * Returns the [`HotCold`]s and the exit [`Node`].
     */
    pub fn hot_path(&self) -> (Vec<HotCold>, Node) {
        let mut cft = self;
        let mut hot_colds = Vec::new();
        loop {
            match cft {
                &CFT::Merge {exit, ..} => {
                    return (hot_colds, exit);
                },
                &CFT::Switch {guard, hot_index, ref cases, ref default_} => {
                    let hot_cold = HotCold::new(guard, hot_index, cases, default_);
                    cft = hot_cold.hot;
                    hot_colds.push(hot_cold);
                },
            }
        }
    }
}
