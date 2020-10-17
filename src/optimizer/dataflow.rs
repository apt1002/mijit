use std::cmp::{max};
use std::collections::{HashMap};
use std::fmt::{Debug};
use std::hash::{Hash};
use crate::util::{RcEq};

use super::{code};
use code::{Value, Precision, UnaryOp, BinaryOp, Width, AliasMask, Action};

/** The latencies of common instructions, in clock cycles. */
pub mod latency {
    pub const ALU: usize = 1;
    pub const AGU: usize = 3;
    pub const CMOV: usize = 2;
    pub const MUL: usize = 3;
}

//-----------------------------------------------------------------------------

/**
 * The unit of instruction reordering and scheduling.
 * Ops are often single instructions.
 * R is the type of word-sized operands.
 * T is the type of zero-sized dependencies, e.g. memory ordering.
 */
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Op<R, T> {
    Input(Value),
    Constant(Precision, i64),
    Unary(UnaryOp, Precision, R),
    Binary(BinaryOp, Precision, R, R),
    Load((Width, R), Vec<T>, AliasMask),
    Store((Width, R), R, Vec<T>, AliasMask),
    Push(R, Option<T>),
    Pop(Option<T>),
    Debug(R, Option<T>),
}
use Op::*;

impl<R, T> Op<R, T> {
    /** Returns all the operands of this Op, and their latencies in cycles. */
    pub fn operands(&self) -> Vec<(&R, usize)> {
        use latency::*;
        use UnaryOp::*;
        use BinaryOp::*;
        match self {
            &Unary(op, _, ref x) => match op {
                Abs => vec![(x, latency::CMOV)],
                Negate | Not => vec![(x, ALU)],
            },
            &Binary(op, _, ref x, ref y) => match op {
                Add | Sub | Lsl | Lsr | Asr | And | Or | Xor => vec![(x, ALU), (y, ALU)],
                Mul => vec![(x, MUL), (y, MUL)],
                Lt | Ult | Eq | Max | Min => vec![(x, CMOV), (y, CMOV)],
            },
            &Load((_, ref addr), _, _) => vec![(addr, AGU)],
            &Store((_, ref addr), ref x, _, _) => vec![(addr, AGU), (x, ALU)],
            &Push(ref x, _) => vec![(x, ALU)],
            &Debug(ref x, _) => vec![(x, ALU)],
            _ => vec![],
        }
    }

    /** Returns all the non-dataflow dependencies of this Op. */
    pub fn dependencies(&self) -> Vec<&T> {
        match self {
            &Load((_, _), ref ts, _) => ts.iter().collect(),
            &Store((_, _), _, ref ts, _) => ts.iter().collect(),
            &Push(_, ref t) => t.iter().collect(),
            &Pop(ref t) => t.iter().collect(),
            &Debug(_, ref t) => t.iter().collect(),
            _ => vec![],
        }
    }

    /** Returns the amount of execution resources needed to execute this Op. */
    pub fn cost(&self) -> usize {
        // For now, just count the x86 instructions in the best case.
        use UnaryOp::*;
        use BinaryOp::*;
        match self {
            &Input(_) => 0,
            &Unary(op, _, _) => match op {
                Abs => 3,
                Negate => 2,
                Not => 1,
            },
            &Binary(op, _, _, _) => match op {
                Add | Sub | Mul | Lsl | Lsr | Asr | And | Or | Xor => 1,
                Lt | Ult | Eq | Max | Min => 3,
            },
            &Debug(_, _) => 0, // Pretend that debugging is free.
            _ => 1,
        }
    }
}

//-----------------------------------------------------------------------------

/**
 * A node of the dataflow graph represents an Op, and relates it to other Ops
 * that must be executed earlier.
 */
#[derive(Debug)]
pub struct Node {
    /** The Op represented by this Node. */
    pub op: Op<RcEq<Node>, RcEq<Node>>,
    /**
     * The number of clock cycles needed to evaluate this Node and all its
     * dependencies, given infinite parallelism.
     */
    pub depth: usize,
    /**
     * The number of stack slots needed to evaluate this Node and all its
     * dependencies, on a pure sequential stack machine, without sharing any
     * subexpressions.
     */
    pub breadth: usize,
}

impl Node {
    pub fn new(
        op: Op<RcEq<Node>, RcEq<Node>>,
    ) -> Self {
        let mut depth = 0;
        let mut breadths = Vec::new();
        for (operand, latency) in op.operands() {
            depth = max(depth, operand.depth + latency);
            breadths.push(operand.breadth);
        }
        breadths.sort();
        let mut breadth = 0;
        for i in 0..breadths.len() {
            breadth = max(breadth, breadths.len() - i + breadths[i]);
        }
        Node {op, depth, breadth}
    }
}

//-----------------------------------------------------------------------------

/**
 * Represents the state of a simulated execution of some [`code::Action`]s.
 */
#[derive(Debug)]
pub struct Simulation {
    /** Maps each Value to the corresponding [`Node`], if any. */
    bindings: HashMap<Value, RcEq<Node>>,
    /** The most recent Store instruction, if any. */
    store: Option<RcEq<Node>>,
    /** All memory accesses instructions since `store`, including `store`. */
    loads: Vec<RcEq<Node>>,
    /** The most recent stack operation, if any. */
    stack: Option<RcEq<Node>>,
}

impl Simulation {
    pub fn new() -> Self {
        // TODO: Take a list of live values and make Op::Inputs for them.
        Simulation {
            bindings: HashMap::new(),
            store: None,
            loads: Vec::new(),
            stack: None,
        }
    }

    /** Bind `value` to `node`. */
    pub fn bind(&mut self, value: Value, node: RcEq<Node>) {
        self.bindings.insert(value, node);
    }

    /** Returns the `Node` bound to `value`, or a fresh `Input`. */
    pub fn lookup(&mut self, value: Value) -> RcEq<Node> {
        self.bindings.entry(value).or_insert_with(|| {
            // TODO: Panic.
            RcEq::new(Node::new(Op::Input(value)))
        }).clone()
    }

    /** Returns a Node representing the result of `op`. */
    fn op(&mut self, op: Op<RcEq<Node>, RcEq<Node>>) -> RcEq<Node> {
        // TODO: CSE.
        RcEq::new(Node::new(op))
    }

    pub fn action(&mut self, action: Action) {
        match action {
            Action::Constant(prec, dest, value) => {
                let node = self.op(Op::Constant(prec, value));
                self.bind(dest, node);
            },
            Action::Move(dest, src) => {
                let node = self.lookup(src);
                self.bind(dest, node);
            },
            Action::Unary(op, prec, dest, src) => {
                let src = self.lookup(src);
                let node = self.op(Op::Unary(op, prec, src));
                self.bind(dest, node);
            },
            Action::Binary(op, prec, dest, src1, src2) => {
                let src1 = self.lookup(src1);
                let src2 = self.lookup(src2);
                let node = self.op(Op::Binary(op, prec, src1, src2));
                self.bind(dest, node);
            },
            Action::Division(_op, _prec, _, _, _, _) => {
                panic!("FIXME: Don't know how to do division");
            },
            Action::Load(dest, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let addr = self.lookup(addr);
                let deps: Vec<_> = self.store.iter().cloned().collect();
                let node = self.op(Op::Load((width, addr), deps, alias_mask));
                self.loads.push(node.clone());
                self.bind(dest, node);
            },
            Action::Store(src, (addr, width), alias_mask) => {
                // TODO: Use AliasMask.
                let src = self.lookup(src);
                let addr = self.lookup(addr);
                let mut deps = vec![];
                std::mem::swap(&mut deps, &mut self.loads);
                let node = self.op(Op::Store((width, addr), src, deps, alias_mask));
                self.loads.push(node.clone());
                self.store = Some(node);
            },
            Action::Push(src) => {
                let src = self.lookup(src);
                let node = self.op(Op::Push(src, self.stack.clone()));
                self.stack = Some(node);
            },
            Action::Pop(dest) => {
                let node = self.op(Op::Pop(self.stack.clone()));
                self.bind(dest, node.clone());
                self.stack = Some(node);
            },
            Action::Debug(src) => {
                let src = self.lookup(src);
                let node = self.op(Op::Debug(src, self.stack.clone()));
                self.stack = Some(node);
            },
        };
    }
}
