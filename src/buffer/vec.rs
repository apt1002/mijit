use std::ops::{Deref, DerefMut};
use super::{Buffer};

#[allow(clippy::module_name_repetitions)]
pub struct VecU8 {
    buffer: Vec<u8>,
    pos: usize,
}

impl VecU8 {
    pub fn new(buffer: Vec<u8>) -> Self {
        VecU8 {buffer: buffer, pos: 0}
    }
}

impl Deref for VecU8 {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &*self.buffer
    }
}

impl DerefMut for VecU8 {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.buffer
    }
}

impl Buffer for VecU8 {
    fn get_pos(&self) -> usize { self.pos }
    fn set_pos(&mut self, pos: usize) { self.pos = pos; }
}
