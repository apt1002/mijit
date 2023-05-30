//! A utility for building programs using a structured programming style.
//! [`Builder`] wraps a [`Dataflow`] and adds [`Node`]s to it. Simultaneously,
//! it builds a [`CFT`], which it ultimately returns.
//!
//! You can ignore this module and build `Node`s and `CFT`s in any way you
//! like, but if you are writing code by hand to construct them then this
//! module might be useful.

use super::{code, Op, Dataflow, Node, CFT, Exit, Switch};
use code::{UnaryOp, BinaryOp, Precision, Width};
use Precision::*;

/// Wraps a closure that builds a control-flow subtree.
///
/// This is an argument type of various control-flow instructions. The closure
/// lives for `'a`, takes an argument of type `Builder<'b, L>` for any `'b`,
/// and returns a `CFT<L>`.
///
/// # Example
///
/// ```
/// # use mijit::graph::{Subtree, Builder};
/// /// Constructs a `Subtree` that jumps to `leaf` passing no values.
/// fn jump_subtree<'a, L: 'a + Clone>(leaf: L) -> Subtree<'a, L> {
///     (|b: Builder<L>| { b.jump(leaf, []) }).into()
/// }
/// ```
pub struct Subtree<'a, L: Clone>(Box<dyn 'a + for<'b> FnOnce(Builder<'b, L>) -> CFT<L>>);

impl<'a, L: Clone, F: 'a> From<F> for Subtree<'a, L>
where F: for<'b> FnOnce(Builder<'b, L>) -> CFT<L>
{
    fn from(f: F) -> Self { Subtree(Box::new(f)) }
}

//-----------------------------------------------------------------------------

/// Represents everything that was built up to and including a [`guard()`].
///
/// [`guard()`]: Builder::guard
#[derive(Debug)]
struct Guard<L: Clone> {
    pub guard: Node,
    pub expected: bool,
    pub if_fail: CFT<L>,
}

//-----------------------------------------------------------------------------

/// A utility for building [`CFT`]s. `T` is usually [`EntryId`].
///
/// [`EntryId`]: crate::jit::EntryId
#[derive(Debug)]
pub struct Builder<'d, L: Clone> {
    /// The [`Dataflow`] that collects the [`Node`]s we build.
    pub dataflow: &'d mut Dataflow,
    /// The most recent `Guard` or `Debug`.
    sequence: Node,
    /// One per call to `guard()`.
    guards: Vec<Guard<L>>,
}

impl<'d, L: Clone> Builder<'d, L> {
    /// Constructs a `Builder`
    /// - dataflow - The [`Dataflow`] that collects the [`Node`]s we build.
    /// - sequence - The most recent [`Guard`] or [`Debug`] [`Node`], or
    ///   `dataflow.undefined()`.
    ///
    /// [`Guard`]: Op::Guard
    /// [`Debug`]: Op::Debug
    pub fn new(dataflow: &'d mut Dataflow, sequence: Node) -> Self {
        Builder {dataflow, sequence, guards: Vec::new()}
    }

    /// Constructs a `Builder` that builds a control-flow subtree.
    /// The returned `Builder` reborrows the same [`Dataflow`] as `self`.
    fn nested(&mut self) -> Builder<'_, L> {
        Builder {dataflow: self.dataflow, sequence: self.sequence, guards: Vec::new()}
    }

    /// Assembles a `Node` whose result is `value`.
    pub fn const_(&mut self, value: i64) -> Node {
        self.dataflow.add_node(Op::Constant(value), &[])
    }

    /// Assembles a `Node` to compute `op(src)`.
    pub fn unary64(&mut self, op: UnaryOp, src: Node) -> Node {
        self.dataflow.add_node(Op::Unary(P64, op), &[src])
    }

    /// Assembles a `Node` to compute `op(src)`
    pub fn unary32(&mut self, op: UnaryOp, src: Node) -> Node {
        self.dataflow.add_node(Op::Unary(P32, op), &[src])
    }

    /// Assembles a `Node` to compute `op(src1, src2)`.
    pub fn binary64(&mut self, op: BinaryOp, src1: Node, src2: Node) -> Node {
        self.dataflow.add_node(Op::Binary(P64, op), &[src1, src2])
    }

    /// Assembles a `Node` to compute `op(src1, src2)`.
    pub fn binary32(&mut self, op: BinaryOp, src1: Node, src2: Node) -> Node {
        self.dataflow.add_node(Op::Binary(P32, op), &[src1, src2])
    }

    /// Assembles `Node`s to compute `op(src, value)`.
    pub fn const_binary64(&mut self, op: BinaryOp, src: Node, value: i64) -> Node {
        let temp = self.const_(value);
        self.binary64(op, src, temp)
    }

    /// Assembles `Node`s to compute `op(src, value)`.
    /// [`TEMP`] is corrupted.
    pub fn const_binary32(&mut self, op: BinaryOp, src: Node, value: i32) -> Node {
        let temp = self.const_(value as i64);
        self.binary32(op, src, temp)
    }

    /// Assembles a `Node` to send memory accesses from `src` to `dest`.
    /// The caller must hereafter use the returned `Node` instead of `dest`.
    pub fn send(&mut self, dest: Node, src: Node) -> Node {
        self.dataflow.add_node(Op::Send, &[dest, src])
    }

    /// Assembles a `Node` to load from address `addr.0 + addr.1`.
    /// The returned `Node` represents the value loaded.
    pub fn load(&mut self, addr: (Node, i32, Width)) -> Node {
        let (base, offset, width) = addr;
        self.dataflow.add_node(Op::Load(offset, width), &[self.sequence, base])
    }

    /// Assembles a `Node` to store `src` at `addr.0 + addr.1`.
    /// The caller must hereafter use the returned `Node` instead of `addr.0`.
    pub fn store(&mut self, src: Node, addr: (Node, i32, Width)) -> Node {
        let (base, offset, width) = addr;
        self.dataflow.add_node(Op::Store(offset, width), &[self.sequence, src, base])
    }

    /// Assembles a [`Node`] that prints out the value of `src`.
    pub fn debug(&mut self, src: Node) {
        self.sequence = self.dataflow.add_node(Op::Debug, &[self.sequence, src]);
    }

    /// Assemble code to check that `condition` is `expected`, and if not, to
    /// abort by running `if_fail`.
    /// See also [`Self::if_()`] which is more symmetrical.
    pub fn guard<'a>(&mut self, condition: Node, expected: bool, if_fail: impl Into<Subtree<'a, L>>) {
        self.sequence = self.dataflow.add_node(Op::Guard, &[self.sequence, condition]);
        let if_fail = if_fail.into().0(self.nested());
        self.guards.push(Guard {guard: self.sequence, expected, if_fail});
    }

    /// Consume this `Builder` and return the finished `CFT`.
    /// Usually, you will prefer to call one of [`Self::jump()`],
    /// [`Self::index()`] or [`Self::if_()`] which call this.
    pub fn finish(mut self, ending: CFT<L>) -> CFT<L> {
        let mut ret = ending;
        while let Some(Guard {guard, expected, if_fail}) = self.guards.pop() {
            let (switch, hot_index) = if expected {
                (Switch::if_(ret, if_fail), usize::MAX)
            } else {
                (Switch::if_(if_fail, ret), 0)
            };
            ret = CFT::Switch {guard, switch, hot_index};
        }
        ret
    }

    /// Assembles code to jump to `leaf` obeying `exit`.
    /// Equivalent to `finish(CFT::Merge { ... })`.
    pub fn jump(self, leaf: L, outputs: impl Into<Box<[Node]>>) -> CFT<L> {
        let exit = Exit {sequence: self.sequence, outputs: outputs.into()};
        self.finish(CFT::Merge {exit, leaf})
    }

    /// Assembles code to select a continuation based on `switch`.
    /// Equivalent to `finish(CFT::Switch { ... })`.
    /// Usually, you will prefer to call one of [`Self::index()`] or
    /// [`Self::if_()`] which call this.
    pub fn switch(
        mut self,
        discriminant: Node,
        switch: Switch<Subtree<L>>,
    ) -> CFT<L> {
        self.sequence = self.dataflow.add_node(Op::Guard, &[self.sequence, discriminant]);
        let switch = switch.map_once(|subtree| subtree.0(self.nested()));
        let ending = CFT::Switch {guard: self.sequence, switch, hot_index: 0 /* TODO */};
        self.finish(ending)
    }

    /// Assembles code to select one of `cases` based on `discriminant`.
    /// Select `default_` if `discriminant` exceeds `cases.len()`.
    /// Equivalent to `switch(discriminant, Switch::new(cases, default_), hot_index)`.
    pub fn index<'a>(
        self,
        discriminant: Node,
        cases: impl Into<Box<[Subtree<'a, L>]>>,
        default_: impl Into<Subtree<'a, L>>,
    ) -> CFT<L> {
        let switch = Switch::new(cases.into(), default_.into());
        self.switch(discriminant, switch)
    }

    /// Assembles code to select `if_true` if `condition` is non-zero,
    /// otherwise `if_false`.
    /// Equivalent to `switch(condition, Switch::if_(if_true, if_false), hot_index)`.
    /// See also `guard()` which favours one outcome.
    pub fn if_<'a>(
        self,
        condition: Node,
        if_true: impl Into<Subtree<'a, L>>,
        if_false: impl Into<Subtree<'a, L>>,
    ) -> CFT<L> {
        let switch = Switch::if_(if_true.into(), if_false.into());
        self.switch(condition, switch)
    }
}
