//! A utility for building [`EBB`]s using a structured programming style.
//! You can ignore this module and build `EBB`s in any way you like, but
//! if you are writing code by hand to construct `EBB`s then this module might
//! be useful.

use super::{
    UnaryOp, BinaryOp, Precision, Width,
    Register, REGISTERS, Variable,
    Action, Switch, EBB, Ending,
};
use Precision::*;
use BinaryOp::*;

/// `REGISTERS[0]` is reserved for use by the `Builder`. Many methods of
/// `Builder` assemble code that corrupts it.
pub const TEMP: Register = REGISTERS[0];

/// Build an EBB. Equivalent to `callback(Builder::new())`.
pub fn build<T>(callback: impl FnOnce(Builder<T>) -> EBB<T>) -> EBB<T> {
    callback(Builder::new())
}

/// Similar to `build()` but only builds a basic block.
// TODO: Use `Builder<!>` not `Builder<()>` when the `!` type is stabilised.
pub fn build_block(callback: impl FnOnce(&mut Builder<()>)) -> Box<[Action]> {
    let mut b = Builder::new();
    callback(&mut b);
    b.actions.into()
}

//-----------------------------------------------------------------------------

/// Represents everything that was built up to and including a [`guard()`].
#[derive(Debug)]
struct Guard<T> {
    pub actions: Vec<Action>,
    pub condition: Variable,
    pub expected: bool,
    pub if_fail: EBB<T>,
}

//-----------------------------------------------------------------------------

/// Specifies an auto-increment mode for memory accesses.
pub enum Increment {
    /// Increment After.
    IA,
    /// Increment Before.
    IB,
    /// Decrement After.
    DA,
    /// Decrement Before.
    DB,
}

use Increment::*;

//-----------------------------------------------------------------------------

/// A utility for building [`EBB`]s. `T` is usually [`EntryId`].
///
/// [`EntryId`]: mijit::jit::EntryId
#[derive(Debug)]
pub struct Builder<T> {
    /// All [`Action`]s generated since the last call to `guard()`, if any.
    pub actions: Vec<Action>,
    /// One per call to `guard()`.
    guards: Vec<Guard<T>>,
}

impl<T> Builder<T> {
    /// Constructs an initially empty `Builder`.
    pub fn new() -> Self {
        Builder {actions: Vec::new(), guards: Vec::new()}
    }

    /// Assembles an `Action` to move `src` into `dest`.
    pub fn move_(&mut self, dest: impl Into<Variable>, src: impl Into<Variable>) {
        self.actions.push(Action::Move(dest.into(), src.into()));
    }

    /// Assembles an `Action` to move `value` into `dest`.
    pub fn const_(&mut self, dest: impl Into<Register>, value: i64) {
        self.actions.push(Action::Constant(P64, dest.into(), value));
    }

    /// Assembles an `Action` to compute `op(src)` into `dest`.
    pub fn unary64(
        &mut self,
        op: UnaryOp,
        dest: impl Into<Register>,
        src: impl Into<Variable>,
    ) {
        self.actions.push(Action::Unary(op, P64, dest.into(), src.into()));
    }

    /// Assembles an `Action` to compute `op(src)` into `dest`.
    pub fn unary32(
        &mut self,
        op: UnaryOp,
        dest: impl Into<Register>,
        src: impl Into<Variable>,
    ) {
        self.actions.push(Action::Unary(op, P32, dest.into(), src.into()));
    }

    /// Assembles an `Action` to compute `op(src1, src2)` into `dest`.
    pub fn binary64(
        &mut self,
        op: BinaryOp,
        dest: impl Into<Register>,
        src1: impl Into<Variable>,
        src2: impl Into<Variable>,
    ) {
        self.actions.push(Action::Binary(op, P64, dest.into(), src1.into(), src2.into()));
    }

    /// Assembles an `Action` to compute `op(src1, src2)` into `dest`.
    pub fn binary32(
        &mut self,
        op: BinaryOp,
        dest: impl Into<Register>,
        src1: impl Into<Variable>,
        src2: impl Into<Variable>,
    ) {
        self.actions.push(Action::Binary(op, P32, dest.into(), src1.into(), src2.into()));
    }

    /// Assembles `Action`s to compute `op(src, value)` into `dest`.
    /// [`TEMP`] is corrupted if `dest == src`.
    pub fn const_binary64(
        &mut self,
        op: BinaryOp,
        dest: impl Into<Register>,
        src: impl Into<Variable>,
        value: i64,
    ) {
        let dest = dest.into();
        let src = src.into();
        let temp = if src != dest.into() {
            dest
        } else if src != TEMP.into() {
            TEMP
        } else {
            panic!("dest and src cannot both be TEMP");
        };
        self.const_(temp, value);
        self.binary64(op, dest, src, temp);
    }

    /// Assembles `Action`s to compute `op(src, value)` into `dest`.
    /// [`TEMP`] is corrupted if `dest == src`.
    pub fn const_binary32(
        &mut self,
        op: BinaryOp,
        dest: impl Into<Register>,
        src: impl Into<Variable>,
        value: i32,
    ) {
        let dest = dest.into();
        let src = src.into();
        let temp = if src != dest.into() {
            dest
        } else if src != TEMP.into() {
            TEMP
        } else {
            panic!("dest and src cannot both be TEMP");
        };
        self.const_(temp, value as i64);
        self.binary32(op, dest, src, temp);
    }

    /// Assembles `Action`s to load `dest` from address `addr.0 + addr.1`.
    /// [`TEMP`] is corrupted if `dest == addr.0`.
    pub fn load(
        &mut self,
        dest: impl Into<Register>,
        addr: (impl Into<Variable>, i64),
        width: Width,
    ) {
        let dest = dest.into();
        self.const_binary64(Add, dest, addr.0, addr.1);
        self.actions.push(Action::Load(dest, (dest.into(), width)));
    }

    /// Assembles `Action`s to compute `addr.0 + addr.1` into `dest` and to
    /// store `src` at that address.
    /// [`TEMP`] is corrupted.
    pub fn store(
        &mut self,
        src: impl Into<Variable>,
        addr: (impl Into<Variable>, i64),
        width: Width,
    ) {
        self.const_binary64(Add, TEMP, addr.0, addr.1);
        self.actions.push(Action::Store(TEMP, src.into(), (TEMP.into(), width)));
    }

    /// Assembles `Action`s to load `dest` from `addr.0 + width * addr.1`.
    /// [`TEMP`] is corrupted.
    pub fn array_load(
        &mut self,
        dest: impl Into<Register>,
        addr: (impl Into<Variable>, impl Into<Variable>),
        width: Width,
    ) {
        self.const_binary64(Lsl, TEMP, addr.1, width as i64);
        self.binary64(Add, TEMP, addr.0, TEMP);
        self.actions.push(Action::Load(dest.into(), (TEMP.into(), width)));
    }

    /// Assembles `Action`s to compute `addr.0 + width * addr.1` into `dest` and
    /// to store `src` at that address.
    /// [`TEMP`] is corrupted.
    pub fn array_store(
        &mut self,
        src: impl Into<Variable>,
        addr: (impl Into<Variable>, impl Into<Variable>),
        width: Width,
    ) {
        self.const_binary64(Lsl, TEMP, addr.1, width as i64);
        self.binary64(Add, TEMP, addr.0, TEMP);
        self.actions.push(Action::Store(TEMP, src.into(), (TEMP.into(), width)));
    }

    fn increment (
        &mut self,
        increment: Increment,
        addr: Register,
        step: i64,
        callback: impl FnOnce(&mut Self),
    ) {
        match increment {
            IB => { self.const_binary64(Add, addr, addr, step); },
            DB => { self.const_binary64(Sub, addr, addr, step); },
            _ => {},
        }
        callback(self);
        match increment {
            IA => { self.const_binary64(Add, addr, addr, step); },
            DA => { self.const_binary64(Sub, addr, addr, step); },
            _ => {},
        }
    }

    /// Assembles `Action`s to load `dest` from `sp` and to increment `sp` by
    /// one word (4 or 8 bytes).
    /// [`TEMP`] is corrupted.
    pub fn increment_load(
        &mut self,
        increment: Increment,
        dest: impl Into<Register>,
        addr: impl Into<Register>,
        width: Width,
    ) {
        let dest = dest.into();
        let addr = addr.into();
        self.increment(increment, addr, 1 << (width as usize), |b| {
            b.load(dest, (addr, 0), width);
        });
    }

    /// Assembles `Action`s to decrement `sp` by one word (4 or 8 bytes) and to
    /// store `src` at `sp`.
    /// [`TEMP`] is corrupted.
    pub fn increment_store(
        &mut self,
        increment: Increment,
        src: impl Into<Variable>,
        addr: impl Into<Register>,
        width: Width,
    ) {
        let src = src.into();
        let addr = addr.into();
        self.increment(increment, addr, 1 << (width as usize), |b| {
            b.store(src, (addr, 0), width);
        });
    }

    /// Assembles an action that prints out the value of `src`.
    pub fn debug(&mut self, src: impl Into<Variable>) {
        self.actions.push(Action::Debug(src.into()));
    }

    /// Assemble code to check that `condition` is `expected`, and if not, to
    /// abort by running `if_fail`.
    /// See also [`if_()`] which is more symmetrical.
    pub fn guard(&mut self, condition: impl Into<Variable>, expected: bool, if_fail: EBB<T>) {
        let mut actions = Vec::new();
        std::mem::swap(&mut actions, &mut self.actions);
        self.guards.push(Guard {actions, condition: condition.into(), expected, if_fail});
    }

    /// Consume this `Builder` and return the finished `EBB`.
    /// Usually, you will prefer to call one of [`jump()`], [`index()`] or
    /// [`if_()`] which call this.
    pub fn ending(mut self, ending: Ending<T>) -> EBB<T> {
        let mut ret = EBB {actions: self.actions, ending};
        while let Some(Guard {actions, condition, expected, if_fail}) = self.guards.pop() {
            let switch = if expected {
                Switch::if_(ret, if_fail)
            } else {
                Switch::if_(if_fail, ret)
            };
            ret = EBB {actions, ending: Ending::Switch(condition, switch)};
        }
        ret
    }

    /// Assembles code to jump to `target`.
    /// Equivalent to `ending(Ending::Leaf(target))`.
    pub fn jump(self, target: T) -> EBB<T> {
        self.ending(Ending::Leaf(target))
    }

    /// Assembles code to select a continuation based on `switch`.
    /// Equivalent to `ending(Ending::Switch(switch))`.
    /// Usually, you will prefer to call one of [`index()`] or [`if_()`] which
    /// call this.
    pub fn switch(self, discriminant: impl Into<Variable>, switch: Switch<EBB<T>>) -> EBB<T> {
        self.ending(Ending::Switch(discriminant.into(), switch))
    }

    /// Assembles code to select one of `cases` based on `discriminant`.
    /// Select `default_` if `discriminant` exceeds `cases.len()`.
    /// Equivalent to `switch(Switch::new(discriminant, cases, default_))`.
    pub fn index(
        self,
        discriminant: impl Into<Variable>,
        cases: Box<[EBB<T>]>,
        default_: EBB<T>,
    ) -> EBB<T> {
        self.switch(discriminant, Switch::new(cases, default_))
    }

    /// Assembles code to select `if_true` if `condition` is non-zero,
    /// otherwise `if_false`.
    /// Equivalent to `switch(Switch::new(condition, if_true, if_false))`.
    /// See also `guard()` which favours one outcome.
    pub fn if_(
        self,
        condition: impl Into<Variable>,
        if_true: EBB<T>,
        if_false: EBB<T>,
    ) -> EBB<T> {
        self.switch(condition, Switch::if_(if_true, if_false))
    }
}
