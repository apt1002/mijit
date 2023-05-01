/// An untyped 64-bit value.
#[repr(C)]
#[derive(Copy, Clone, Eq)]
pub union Word {
    pub u: u64,
    pub s: i64,
    pub w: std::num::Wrapping<u64>,
    pub p: *const (),
    pub mp: *mut (),
}

impl Default for Word {
    fn default() -> Self { Word {u: 0} }
}

impl std::fmt::Debug for Word {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Word")
            .field("u", &format!("{:#x}", unsafe {self.u}))
            .finish()
    }
}

impl PartialEq for Word {
    fn eq(&self, other: &Self) -> bool {
        unsafe {self.u == other.u}
    }
}
