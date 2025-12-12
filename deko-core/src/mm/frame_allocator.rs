//! Implements a simple page frame allocator.
use deko_std::prelude::*;
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::mm::DEKO_FRAME_ALLOCATOR;

verus! {

/// A simple page frame allocator that allocates physical pages. This just holds a
/// buddy allocator inside where we implement this in `deko_std`.
pub struct DekoPageFrameAllocator(pub DekoBuddyAllocator<DekoHeap<HEAP_SIZE>>);

impl DekoPageFrameAllocator {
    pub open spec fn inv(&self) -> bool {
        self.0.wf()
    }

    pub fn init(&self, phys_start: u64, size: u64)
        requires
            self.wf(),
            size > 0,
            valid_heap_param(phys_start, size, HEAP_SIZE as u64),
            phys_start == (STAGE2_HEAP_START as u64),
            size == (STAGE2_HEAP_END - STAGE2_HEAP_START) as u64,
    {
        self.0.init(phys_start, size);
    }

    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
    {
        let ghost f = DekoHeapPredicate;
        let heap = DekoHeap::<HEAP_SIZE>::new(Ghost(f));

        Self(DekoBuddyAllocator::new(heap, Ghost(f)))
    }
}

impl WellFormed for DekoPageFrameAllocator {
    open spec fn wf(&self) -> bool {
        self.inv()
    }
}

pub struct DekoAllocatorApi;

impl WellFormed for DekoAllocatorApi {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[verifier::external]
unsafe impl core::alloc::Allocator for DekoAllocatorApi {
    #[inline]
    fn allocate(&self, layout: core::alloc::Layout) -> Result<
        core::ptr::NonNull<[u8]>,
        core::alloc::AllocError,
    > {
        DEKO_FRAME_ALLOCATOR.0.allocate(layout)
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: core::alloc::Layout) {
        DEKO_FRAME_ALLOCATOR.0.deallocate(ptr, layout);
    }
}

} // verus!
