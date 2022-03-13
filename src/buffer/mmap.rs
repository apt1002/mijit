use std::ops::{Deref, DerefMut};
use memmap::{MmapMut};
use super::{Buffer};

/**
 * Represents a block of memory claimed from the operating system using
 * `mmap()`. Memory allocated in this way can be made executable.
 */
pub enum Mmap {
    Mut(MmapMut),
    Poisoned,
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
    pub fn execute<T>(&mut self, callback: impl FnOnce(&[u8]) -> T) -> T {
        let mut new_self = Self::Poisoned;
        std::mem::swap(self, &mut new_self);
        match new_self {
            Self::Mut(mut memory) => {
                let executable_memory = memory.make_exec().expect("mprotect failed");
                let result = callback(&executable_memory);
                memory = executable_memory.make_mut().expect("mprotect failed");
                *self = Self::Mut(memory);
                result
            },
            Self::Poisoned => panic!("Poisoned by an earlier error"),
        }
    }
}

impl AsMut<MmapMut> for Mmap {
    fn as_mut(&mut self) -> &mut MmapMut {
        match self {
            Self::Mut(ref mut m) => m,
            Self::Poisoned => panic!("Poisoned by an earlier error"),
        }
    }
}

impl Deref for Mmap {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Mut(ref m) => &*m,
            Self::Poisoned => panic!("Poisoned by an earlier error"),
        }
    }
}

impl DerefMut for Mmap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.as_mut()
    }
}

impl Buffer for Mmap {
    fn new() -> Self {
        let memory = MmapMut::map_anon(0x1000).expect("Out of memory");
        Self::Mut(memory)
    }

    fn resize(&mut self, min_length: usize) {
        let memory: &mut MmapMut = self.as_mut();
        if min_length > memory.len() {
            let mut new_memory = MmapMut::map_anon(min_length).expect("Out of memory");
            new_memory[..memory.len()].copy_from_slice(memory);
            *memory = new_memory;
        }
    }
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
        let mut buffer = Mmap::new();
        let result = buffer.execute(|_bytes| 42);
        assert_eq!(result, 42);
    }
}
