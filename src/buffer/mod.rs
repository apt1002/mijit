use std::ops::{DerefMut};

mod mmap;
pub use mmap::{Mmap};

mod vec;
pub use vec::{VecU8};

pub trait Buffer: Sized + DerefMut<Target=[u8]> {
    /** Allocates a fresh `Buffer` with a default (small) length. */
    fn new() -> Self;

    /**
     * Reallocate this `Buffer` if necessary to ensure that it holds at
     * least `min_length` bytes. Panics if the reallocation fails.
     */
    fn resize(&mut self, min_length: usize);

    /** Get the write pointer. */
    fn get_pos(&self) -> usize;

    /** Set the write pointer. */
    fn set_pos(&mut self, pos: usize);

    /**
     * Writes a single byte at the write pointer, incrementing it.
     * Writes beyond [`len()`] resize the buffer to a power-of-two length.
     */
    fn write_byte(&mut self, byte: u8) {
        let pos = self.get_pos();
        if pos >= self.len() {
            self.resize(std::cmp::max(pos + 1, 0x1000).checked_next_power_of_two().unwrap());
        }
        self[pos] = byte;
        self.set_pos(pos + 1);
    }

    /**
     * Writes up to 8 bytes at the write pointer, as if using
     * [`write_byte()`] repeatedly.
     */
    fn write(&mut self, mut bytes: u64, len: usize) {
        assert!(len <= 8);
        for _ in 0..len {
            self.write_byte(bytes as u8);
            bytes >>= 8;
        }
        assert_eq!(bytes, 0);
    }

    /** Reads a single byte. Reading beyond [`len()`] gives `0`. */
    fn read_byte(&self, pos: usize) -> u8 {
        if pos < self.len() {
            self[pos]
        } else {
            0
        }
    }

    /** Reads up to 8 bytes, as if using [`read_byte()`] repeatedly. */
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

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    /** Any tests of the [`Buffer`] API, for use by submodule tests. */
    pub fn api(_buffer: impl Buffer) {
    }
}
