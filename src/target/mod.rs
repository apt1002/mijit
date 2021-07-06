use super::{buffer, code};

mod pool;
pub use pool::{Counter, Word, Pool};

mod label;
pub use label::{Patch, Label};

mod traits;
pub use traits::{Lower, ExecuteFn, Execute, Target};

pub mod x86_64;

/**
 * The [`Register`] which holds the state index on entry and exit from Mijit.
 * This is guaranteed to be [`REGISTERS`][[`0`]].
 */
// TODO: Somehow hide the state index from this module, and delete this.
pub const STATE_INDEX: code::Register = code::REGISTERS[0];

/** A [`Target`] that generates code which can be executed. */
pub fn native() -> impl Target {
    if cfg!(target_arch="x86_64") {
        x86_64::Target
    } else {
        panic!("FIXME: Unknown target");
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    use code::{Register, REGISTERS, Action, BinaryOp, Precision};
    use Precision::*;

    pub const R0: Register = REGISTERS[0];
    pub const R1: Register = REGISTERS[1];

    #[test]
    fn add5() {
        let target = native();
        let pool = Pool::new(0);
        let mut lo = target.lowerer(pool);
        let start = lo.here();
        lo.prologue();
        lo.action(Action::Constant(P64, R1, 5));
        lo.action(Action::Binary(BinaryOp::Add, P64, R0, R0.into(), R1.into()));
        lo.epilogue();
        let (_lo, result) = lo.execute(&start, |f, pool| {
            f(pool.as_mut().as_mut_ptr(), Word {u: 42})
        }).expect("Couldn't change permissions");
        assert_eq!(result, Word {u: 42 + 5});
    }
}
