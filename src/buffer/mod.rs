use std::ops::{DerefMut};

mod mmap;
pub use mmap::{Mmap};

/// An auto-growing array of bytes. In addition to the usual slice API, methods
/// are provided for reading or writing up to 8 bytes at a time using a `u64`.
///
/// [`Vec<u8>`] implements this trait, which is useful for testing.
///
/// [`Mmap`] implements this trait and allows the bytes to be executed as code.
pub trait Buffer: Sized + DerefMut<Target=[u8]> {
    /// Allocates a fresh `Buffer` with a default (small) length.
    fn new() -> Self;

    /// Reallocate this `Buffer` if necessary to ensure that it holds at
    /// least `min_length` bytes. Panics if the reallocation fails.
    fn resize(&mut self, min_length: usize);

    /// Writes a single byte at `pos`.
    /// Writes beyond the end of the buffer resize it to a power-of-two length.
    fn write_byte(&mut self, pos: usize, byte: u8) {
        if pos >= self.len() {
            self.resize(std::cmp::max(pos + 1, 0x1000).checked_next_power_of_two().unwrap());
        }
        self[pos] = byte;
    }

    /// Writes up to 8 bytes at `pos`, as if using [`write_byte()`] repeatedly,
    /// incrementing `pos` after each call.
    ///
    /// [`write_byte()`]: Self::write_byte
    fn write(&mut self, pos: usize, mut bytes: u64, len: usize) {
        assert!(len <= 8);
        for i in 0..len {
            self.write_byte(pos + i, bytes as u8);
            bytes >>= 8;
        }
        assert_eq!(bytes, 0);
    }

    /// Reads a single byte. Reading beyond the end of the buffer gives `0`.
    fn read_byte(&self, pos: usize) -> u8 {
        if pos < self.len() {
            self[pos]
        } else {
            0
        }
    }

    /// Reads up to 8 bytes, as if using [`read_byte()`] repeatedly.
    ///
    /// [`read_byte()`]: Self::read_byte
    fn read(&self, pos: usize, len: usize) -> u64 {
        assert!(len <= 8);
        let mut bytes: u64 = 0;
        for i in (0..len).rev() {
            bytes <<= 8;
            bytes |= u64::from(self.read_byte(pos + i));
        }
        bytes
    }
}

impl Buffer for Vec<u8> {
    fn new() -> Self { Vec::new() }

    fn resize(&mut self, min_length: usize) {
        self.resize(min_length, 0);
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    /// Any tests of the [`Buffer`] API, for use by submodule tests.
    pub fn api(mut buffer: impl Buffer) {
        buffer.resize(16);
        let len = buffer.len();
        buffer.write(4, 0x0001020304050607, 8);
        assert_eq!(buffer.read(4, 8), 0x0001020304050607);
        assert_eq!(buffer.read(len+4, 8), 0);
        buffer.write(len+4, 0x08090A0B0C0D0E0F, 8);
        assert!(buffer.len() >= len+12);
        assert_eq!(buffer.read(4, 8), 0x0001020304050607);
        assert_eq!(buffer.read(len+4, 8), 0x08090A0B0C0D0E0F);
    }

    #[test]
    fn vec() {
        api(Vec::<u8>::new());
    }
}
