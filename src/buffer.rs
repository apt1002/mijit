extern crate memmap;

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
    
}