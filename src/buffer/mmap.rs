use std::ops::{Deref, DerefMut};
use memmap::{MmapMut};
use super::{Buffer};

/**
 * Represents a block of memory claimed from the operating system using
 * `mmap()`. Memory allocated in this way can be made executable.
 */
pub struct Mmap {
    memory: MmapMut,
    /// The write pointer: an index into `memory`.
    pos: usize,
}

impl Mmap {
    /**
     * Make this [`Mmap`] executable, pass it to `callback`, then make it
     * writeable again.
     *
     * If we can't change the buffer permissions, you get an [`Err`] and the [`Mmap`]
     * is gone. T can itself be a Result if necessary to represent errors
     * returned by `callback`
     */
    pub fn execute<T>(mut self, callback: impl FnOnce(&[u8]) -> T)
    -> std::io::Result<(Self, T)> {
        let executable_memory = self.memory.make_exec()?;
        let result = callback(&executable_memory);
        self.memory = executable_memory.make_mut()?;
        Ok((self, result))
    }
}

impl Deref for Mmap {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &*self.memory
    }
}

impl DerefMut for Mmap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.memory
    }
}

impl Buffer for Mmap {
    fn new() -> Self {
        let memory = MmapMut::map_anon(0x1000).expect("Out of memory");
        Mmap {memory, pos: 0}
    }

    fn resize(&mut self, min_length: usize) {
        if min_length > self.len() {
            let mut new_memory = MmapMut::map_anon(min_length).expect("Out of memory");
            new_memory[..self.len()].copy_from_slice(&self.memory);
            self.memory = new_memory
        }
    }

    fn get_pos(&self) -> usize { self.pos }
    fn set_pos(&mut self, pos: usize) { self.pos = pos; }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn api() {
        let buffer = Mmap::new();
        super::super::tests::api(buffer)
    }

    #[test]
    fn execute() {
        let buffer = Mmap::new();
        let (_buffer, result) = buffer.execute(|_bytes| 42)
            .expect("Couldn't change permissions");
        assert_eq!(result, 42);
    }
}
