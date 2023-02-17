use std::collections::{HashMap};
use std::fmt::{Debug};

use super::{Switch, Node};

//-----------------------------------------------------------------------------

/// Helper for formatting [`Cold`]s.
enum CaseAdapter<C> {
    Hot,
    Cold(C),
}

impl<C: Debug> Debug for CaseAdapter<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        if let CaseAdapter::Cold(ref c) = self {
            c.fmt(f)
        } else {
            f.write_str("(hot path)")
        }
    }
}

//-----------------------------------------------------------------------------

/// The cold (less common) branches of a control-flow decision, along with the
/// information needed to combine them with the hot branch to reconstruct the
/// whole [`Switch`].
///
/// This is used in the return types of [`Switch::remove_hot()`] and
/// [`CFT::hot_path()`].
#[derive(Clone, PartialEq, Eq)]
pub struct Cold<C> {
    /// The index of the most probable case, or `usize::MAX`.
    pub hot_index: usize,
    /// A `C` for each cold branch (omitting the hot branch).
    pub colds: Box<[C]>,
}

impl<C> Cold<C> {
    /// Separates the hot and cold branches of a `Switch`.
    pub fn new(switch: Switch<C>, hot_index: usize) -> (C, Self) {
        let Switch {cases, default_} = switch;
        let mut cases = cases.into_vec();
        let hot = if hot_index == usize::MAX {
            *default_
        } else {
            let hot = cases.remove(hot_index);
            cases.push(*default_);
            hot
        };
        let colds = cases.into_boxed_slice();
        (hot, Cold {hot_index, colds})
    }

    /// Apply `callback` to every `C` and return a fresh `Cold`.
    pub fn map<'a, D>(&'a self, mut callback: impl FnMut(&'a C) -> D) -> Cold<D> {
        let Cold {hot_index, ref colds} = *self;
        let colds = colds.iter().map(&mut callback).collect();
        Cold {hot_index, colds}
    }

    /// Recombines the hot and cold branches.
    pub fn finish(self, hot: C) -> Switch<C> {
        let Cold {hot_index, colds} = self;
        let mut colds: Vec<C> = colds.into_vec();
        let default_ = Box::new(if hot_index == usize::MAX {
            hot
        } else {
            let default_ = colds.pop().unwrap();
            colds.insert(hot_index, hot);
            default_
        });
        let cases = colds.into_boxed_slice();
        Switch {cases, default_}
    }

    /// Returns a [`Switch`] with a dummy value in place of the hot case.
    pub fn debug<'a>(&'a self) -> Switch<impl 'a + Debug> where C: Debug {
        self.map(|c| CaseAdapter::Cold(c)).finish(CaseAdapter::Hot)
    }
}

impl<C: Debug> Debug for Cold<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let switch = self.debug();
        f.debug_struct("Cold")
            .field("cases", &switch.cases)
            .field("default_", &switch.default_)
            .finish()
    }
}

//-----------------------------------------------------------------------------

/// Represents a control-flow tree.
#[derive(Debug, Clone)]
pub enum CFT<L: Clone> {
    Merge {
        /// The exit [`Node`] of the dataflow graph for this path.
        exit: Node,
        /// Where to merge into the existing compiled code.
        leaf: L,
    },
    Switch {
        /// The [`Op::Guard`] that discriminates the cases.
        guard: Node,
        /// The control-flow decision.
        switch: Switch<CFT<L>>,
        /// The index of the most probable case, or `usize::MAX`.
        hot_index: usize,
    },
}

impl<L: Clone> CFT<L> {
    /// Constructs a `CFT::Switch`.
    pub fn switch(
        guard: Node,
        cases: impl Into<Box<[CFT<L>]>>,
        default_: impl Into<Box<CFT<L>>>,
        hot_index: usize,
    ) -> Self {
        let switch = Switch {cases: cases.into(), default_: default_.into()};
        CFT::Switch {guard, switch, hot_index}
    }

    /// Follows the hot path through `self`.
    /// Returns the [`Colds`]es and the exit [`Node`].
    pub fn hot_path(&self) -> (HashMap<Node, Cold<&Self>>, Node, L) {
        let mut cft = self;
        let mut colds = HashMap::new();
        loop {
            match cft {
                &CFT::Merge {exit, ref leaf} => {
                    return (colds, exit, leaf.clone());
                },
                &CFT::Switch {guard, ref switch, hot_index} => {
                    let (hot, cold) = Cold::new(switch.map(|t| t), hot_index);
                    cft = hot;
                    colds.insert(guard, cold);
                },
            }
        }
    }
}
