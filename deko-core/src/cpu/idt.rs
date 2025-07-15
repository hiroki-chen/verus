use vstd::prelude::*;

verus! {

/// The base addresses of the IDT should be aligned on an 8-byte boundary
/// to maximize performance of cache line fills.
#[repr(C, packed(8))]
pub struct IdtEntry {
    low: u64,
    high: u64,
}

impl IdtEntry {
    pub const fn no_handler() -> Self {
        Self { low: 0, high: 0 }
    }
}

} // verus!
