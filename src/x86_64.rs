/*
pub use std::fmt::{Debug};

pub enum Error {
    OutOfMemory,
    Other(&'static dyn std::error::Error),
}

impl std::error::Error for Error {
}

/** A placeholder. I'm not sure what will implement this, but whatever it is,
 * we should probably move all the methods there and delete this trait. */
pub trait Buffer {
    fn write1(&mut self) -> Result;
}
*/

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Register(usize);

pub const A: Register = Register(0);
pub const D: Register = Register(1);
pub const C: Register = Register(2);
pub const B: Register = Register(3);
//pub const SP: Register = Register(4);
pub const BP: Register = Register(5);
pub const SI: Register = Register(6);
pub const DI: Register = Register(7);

pub const ALLOCATABLE_REGISTERS: [Register; 4] = [A, D, C, B];

//-----------------------------------------------------------------------------

#[cfg(test)]
pub mod tests {
    use iced_x86::{Decoder, Formatter, NasmFormatter};

    /**
     * Disassemble the given x64_64 `code_bytes` as if they were at `code_ip`.
     */
    pub fn disassemble(code_bytes: &[u8], code_ip: u64) -> Vec<String> {
        let mut decoder = Decoder::new(64, code_bytes, 0);
        decoder.set_ip(code_ip);
        let mut formatter = NasmFormatter::new();
        decoder.iter().map(|instruction| {
            let ip = instruction.ip();
            let start = (ip - code_ip) as usize;
            let len = instruction.len() as usize;
            let bytes = code_bytes[start..][..len].iter().rev().map(
                |b| format!("{:02X}", b)
            ).collect::<Vec<String>>().join(" ");
            let mut assembly = String::with_capacity(80);
            formatter.format(&instruction, &mut assembly);
            format!("{:016X}   {:>23}   {:}", ip, bytes, assembly)
        }).collect()
    }

    #[test]
    fn test_disassemble() {
        let example_code = &[0x48, 0x89, 0x5C, 0x24, 0x10, 0x55];
        assert_eq!(disassemble(example_code, 0x10000000), [
            "0000000010000000            10 24 5C 89 48   mov [rsp+10h],rbx",
            "0000000010000005                        55   push rbp",
        ]);
    }
}
