use std::fmt::{Debug};
use super::{Node};

//-----------------------------------------------------------------------------

/// Represents a control flow decision. Analogous to [`code::Switch`].
///
/// `code::Switch`: super::code::Switch
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Switch<C> {
    /// The [`Op::Guard`] that discriminates the cases.
    pub guard: Node,
    /// The numbered cases.
    pub cases: Box<[C]>,
    /// The default case.
    pub default_: Box<C>,
}

impl<C> Switch<C> {
    /// Apply `callback` to every `C` and return a fresh `Switch`.
    pub fn map<'a, D>(&'a self, mut callback: impl FnMut(&'a C) -> D) -> Switch<D> {
        let Switch {guard, ref cases, ref default_} = *self;
        let cases = cases.iter().map(&mut callback).collect();
        let default_ = Box::new(callback(default_));
        Switch {guard, cases, default_}
    }

    /// Separates the hot and cold branches.
    pub fn remove_hot(self, hot_index: usize) -> (C, Cold<C>) {
        let Switch {guard, cases, default_} = self;
        let mut cases = cases.into_vec();
        let hot = if hot_index == usize::MAX {
            *default_
        } else {
            let hot = cases.remove(hot_index);
            cases.push(*default_);
            hot
        };
        let colds = cases.into_boxed_slice();
        (hot, Cold {guard, hot_index, colds})
    }
}

//-----------------------------------------------------------------------------

/// The cold (less common) branches of a control-flow decision, along with the
/// information needed to combine them with the hot branch to reconstruct the
/// whole [`Switch`].
///
/// This is used in the return types of [`Switch::remove_hot()`] and
/// [`CFT::hot_path()`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cold<C> {
    /// The [`Op::Guard`] that separates these `Colds` from the hot path.
    pub guard: Node,
    /// The index of the most probable case, or `usize::MAX`.
    pub hot_index: usize,
    /// A `C` for each cold branch (omitting the hot branch).
    pub colds: Box<[C]>,
}

impl<C> Cold<C> {
    /// Apply `callback` to every `C` and return a fresh `Cold`.
    pub fn map<'a, D>(&'a self, mut callback: impl FnMut(&'a C) -> D) -> Cold<D> {
        let Cold {guard, hot_index, ref colds} = *self;
        let colds = colds.iter().map(&mut callback).collect();
        Cold {guard, hot_index, colds}
    }

    /// Recombines the hot and cold branches.
    pub fn insert_hot(self, hot: C) -> Switch<C> {
        let Cold {guard, hot_index, colds} = self;
        let mut colds: Vec<C> = colds.into_vec();
        let default_ = Box::new(if hot_index == usize::MAX {
            hot
        } else {
            let default_ = colds.pop().unwrap();
            colds.insert(hot_index, hot);
            default_
        });
        let cases = colds.into_boxed_slice();
        Switch {guard, cases, default_}
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
        let cases = cases.into();
        let default_ = default_.into();
        CFT::Switch {switch: Switch {guard, cases, default_}, hot_index}
    }

    /// Follows the hot path through `self`.
    /// Returns the [`Colds`]es and the exit [`Node`].
    pub fn hot_path(&self) -> (Vec<Cold<&Self>>, Node, L) {
        let mut cft = self;
        let mut colds = Vec::new();
        loop {
            match cft {
                &CFT::Merge {exit, ref leaf} => {
                    return (colds, exit, leaf.clone());
                },
                &CFT::Switch {ref switch, hot_index} => {
                    let (hot, cold) = switch.map(|t| t).remove_hot(hot_index);
                    cft = hot;
                    colds.push(cold);
                },
            }
        }
    }
}
