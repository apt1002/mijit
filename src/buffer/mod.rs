use std::ops::{DerefMut};

mod mmap;
pub use mmap::{Mmap};

pub trait Buffer: DerefMut<Target=[u8]> {}

impl Buffer for Vec<u8> {}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    /** Any tests of the [`Buffer`] API, for use by submodule tests. */
    pub fn api(_buffer: impl Buffer) {
    }
}
