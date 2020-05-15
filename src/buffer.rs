extern crate memmap;

use memmap::{MmapMut};

#[repr(C)]
pub struct Buffer {
    memory: MmapMut,
    used: usize,
}

impl Buffer {
    /** Allocates a Buffer. Returns `None` if not possible. */
    pub fn new(capacity: usize) -> Option<Self> {
        match MmapMut::map_anon(capacity) {
            Ok(memory) => Some(Buffer {memory, used: 0}),
            Err(_) => None
        }
    }
}
