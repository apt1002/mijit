/** Represents an `A` or a `B` or both. */
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum AndOr<A, B> {
    A(A),
    B(B),
    AB(A, B),
}

use AndOr::*;

impl<A, B> AndOr<A, B> {
    /** Returns the `A` if possible, otherwise the `B`. */
    pub fn a(&self) -> Result<&A, &B> {
        match *self {
            A(ref a) => Ok(a),
            B(ref b) => Err(b),
            AB(ref a, _) => Ok(a),
        }
    }

    /** Returns the `B` if possible, otherwise the `A`. */
    pub fn b(&self) -> Result<&B, &A> {
        match *self {
            A(ref a) => Err(a),
            B(ref b) => Ok(b),
            AB(_, ref b) => Ok(b),
        }
    }

    /** Returns the `A` if possible, otherwise the `B`. */
    pub fn a_mut(&mut self) -> Result<&mut A, &mut B> {
        match *self {
            A(ref mut a) => Ok(a),
            B(ref mut b) => Err(b),
            AB(ref mut a, _) => Ok(a),
        }
    }

    /** Returns the `B` if possible, otherwise the `A`. */
    pub fn b_mut(&mut self) -> Result<&mut B, &mut A> {
        match *self {
            A(ref mut a) => Err(a),
            B(ref mut b) => Ok(b),
            AB(_, ref mut b) => Ok(b),
        }
    }
}
