use std::ops::{Deref, DerefMut};
use memmap::{MmapMut};

#[repr(C)]
pub struct Buffer {
    memory: MmapMut,
}

impl Buffer {
    /** Allocates a Buffer. Returns `None` if not possible. */
    pub fn new(capacity: usize) -> Option<Self> {
        match MmapMut::map_anon(capacity) {
            Ok(memory) => Some(Buffer {memory}),
            Err(_) => None
        }
    }

    /**
     * Make this Buffer executable, pass it to `callback`, then make it
     * writeable again.
     *
     * If we can't change the buffer permissions, you get an Err and the Buffer
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

impl Deref for Buffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &*self.memory
    }
}

impl DerefMut for Buffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.memory
    }
}

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn execute() {
        let buffer = Buffer::new(0x1000)
            .expect("Couldn't allocate");
        let (_buffer, result) = buffer.execute(|_bytes| 42)
            .expect("Couldn't change permissions");
        assert_eq!(result, 42);
    }
}