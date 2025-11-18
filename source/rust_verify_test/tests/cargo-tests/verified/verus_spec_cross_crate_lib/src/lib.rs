use vstd::prelude::*;

// Test library that exports a function using verus_spec(with ...)
#[verus_spec(with Tracked(extra): Tracked<u32> -> out: Tracked<u32>)]
pub fn get_data(value: u32) -> u32 {
    proof_with!(|= Tracked(2));
    value
}

// Another function to test the cross-crate _VERUS_VERIFIED call
#[verus_spec(with Ghost(ghost_val): Ghost<u64>)]
pub fn process_data(data: u64) -> u64 {
    data
}
