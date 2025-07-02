use alloc::alloc::{GlobalAlloc, Layout};

use vstd::prelude::*;

use super::Allocator;

verus! {

#[verifier::external]
unsafe impl GlobalAlloc for Allocator {
    #[verifier::external]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unimplemented!("GlobalAlloc::alloc is not implemented in this example");
    }

    #[verifier::external]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unimplemented!("GlobalAlloc::dealloc is not implemented in this example");
    }
}

} // verus!
