/// Beetle's registers.
#[repr(C)]
#[derive(Default)]
pub struct Registers {
    pub ep: u32,
    pub i: u32,
    pub a: u32,
    pub sp: u32,
    pub rp: u32,
}

impl std::fmt::Debug for Registers {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        f.debug_struct("Registers")
            .field("ep", &format!("{:#x}", self.ep))
            .field("i", &format!("{:#x}", self.i))
            .field("a", &format!("{:#x}", self.a))
            .field("sp", &format!("{:#x}", self.sp))
            .field("rp", &format!("{:#x}", self.rp))
            .finish()
    }
}
