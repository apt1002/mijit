use std::cmp::{PartialEq, Eq};
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::{Rc};

/** A thin wrapper around an Rc<T> that uses pointer equality. */
pub struct RcEq<T>(pub Rc<T>);

impl<T> RcEq<T> {
    pub fn new(t: T) -> Self {
        RcEq(Rc::new(t))
    }
}

impl<T> std::ops::Deref for RcEq<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl<T: Debug> Debug for RcEq<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        (*self.0).fmt(f)
    }    
}

impl<T> Clone for RcEq<T> {
    fn clone(&self) -> Self {
        RcEq(self.0.clone())
    }
}

impl<T> Hash for RcEq<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self, state);
    }
}

impl<T> PartialEq for RcEq<T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl<T> Eq for RcEq<T> {}
