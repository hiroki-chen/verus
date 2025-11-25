use core::alloc::Layout;
use core::ptr::NonNull;

use vstd::prelude::*;

verus! {

/// This struct does nothing but just a proxy wrapper so that we
/// can forward the request of [`allocator_api2::alloc::Allocator`]
/// into the unstable allocator APIs.
///
/// This enables some heap-allocated data structures like [`hashbrown`]
/// to be allocated using any struct that implements the trait
/// [`core::alloc::Allocator`].
///
/// For further usages readers may refer to [`super::collections::hashmap`].
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct AllocatorWrapper<A: core::alloc::Allocator>(A);

#[verifier::external]
unsafe impl<A: core::alloc::Allocator> allocator_api2::alloc::Allocator for AllocatorWrapper<A> {
    // Forward methods to core::alloc::Allocator
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, allocator_api2::alloc::AllocError> {
        self.0.allocate(layout).map_err(|_| allocator_api2::alloc::AllocError)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        self.0.deallocate(ptr, layout);
    }
}

} // verus!
