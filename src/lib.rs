extern crate memmap;

use memmap::{MmapMut};

#[repr(C)]
pub struct Buffer {
    memory: MmapMut,
}

#[no_mangle]
pub extern fn mijit_new() -> Option<Box<Buffer>> {
    match MmapMut::map_anon(8) {
        Ok(memory) => Some(Box::new(Buffer {memory})),
        Err(_) => None
    }
}

#[no_mangle]
pub extern fn mijit_drop(_buffer: Box<Buffer>) {}

#[no_mangle]
pub extern fn five(/*buffer: &Buffer*/) -> i64 {
    5 //buffer.memory[0] as i64
}

#[cfg(test)]
mod tests {
    #[test]
    fn five() {
        let f = super::five();
        assert_eq!(f, 5);
    }
}
