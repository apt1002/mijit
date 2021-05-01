use std::ops::{Deref, DerefMut};
use memmap::{MmapMut};
use super::{Buffer};

#[repr(C)]
pub struct Mmap {
    memory: MmapMut,
    /// The write pointer: an index into `memory`.
    pos: usize,
}

impl Mmap {
    /** Allocates an [`Mmap`]. Returns `None` if not possible. */
    pub fn new(capacity: usize) -> std::io::Result<Self> {
        Ok(Mmap {memory: MmapMut::map_anon(capacity)?, pos: 0})
    }

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
    fn get_pos(&self) -> usize { self.pos }
    fn set_pos(&mut self, pos: usize) { self.pos = pos; }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn api() {
        let buffer = Mmap::new(0x1000).expect("Couldn't allocate");
        super::super::tests::api(buffer)
    }

    #[test]
    fn execute() {
        let buffer = Mmap::new(0x1000).expect("Couldn't allocate");
        let (_buffer, result) = buffer.execute(|_bytes| 42)
            .expect("Couldn't change permissions");
        assert_eq!(result, 42);
    }
}
