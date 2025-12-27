//! Implements a simple page frame allocator.
use deko_macros::DekoDebug;
use deko_std::prelude::*;
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::hal::is_stage2;
use crate::mm::{DEKO_FRAME_ALLOCATOR, DEKO_FRAME_ALLOCATOR_FULL};

verus! {

/// This allocator is a thin wrapper around the buddy allocator that
/// manages physical pages; unlike [`DekoAllocatorApi`] which is a
/// type-erased allocator that serves for any heap allocations from
/// [`alloc`] crate.
///
/// This allocator is a main API for allocating kernel-managed heap
/// objects that require physical memory backing, e.g., page tables,
/// stacks, etc.
///
/// # Examples
///
/// ```rust,ignore
///     let (p, Tracked(mut perm)) = deko_std::pptr::DekoPPtr::empty(MY_ALLOCATOR);
///     p.write(Tracked(&mut perm), 42);
/// ```
#[verifier::reject_recursive_types(ORDER)]
pub struct DekoPageFrameAllocator<const ORDER: usize>(pub DekoBuddyAllocator<DekoHeap<ORDER>>);

impl<const ORDER: usize> View for DekoPageFrameAllocator<ORDER> {
    type V = DekoBuddyAllocator<DekoHeap<ORDER>>;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.0
    }
}

impl<const ORDER: usize> DekoFrameAllocator for DekoPageFrameAllocator<ORDER> {
    #[inline]
    fn alloc_page(&self, size: usize, align: usize) -> (r: (
        *mut u8,
        Tracked<PointsToRaw>,
        Tracked<vstd::raw_ptr::Dealloc>,
    )) {
        let (ptr, Tracked(points_to), Tracked(dealloc)) = self.0.alloc(size, align);
        (ptr, Tracked(points_to), Tracked(dealloc))
    }

    #[inline]
    fn dealloc_page(
        &self,
        ptr: *mut u8,
        size: usize,
        align: usize,
        Tracked(perm): Tracked<PointsToRaw>,
        Tracked(dealloc): Tracked<vstd::raw_ptr::Dealloc>,
    ) {
        self.0.dealloc(ptr, size, align, Tracked(perm), Tracked(dealloc));
    }
}

impl<const ORDER: usize> DekoPageFrameAllocator<ORDER> {
    pub fn init(&self, phys_start: u64, size: u64)
        requires
            self.wf(),
            size > 0,
            valid_heap_param(phys_start, size, ORDER as u64),
    {
        self.0.init(phys_start, size, ORDER as u64);
    }

    pub const fn new() -> (r: Self)
        requires
            0 < ORDER <= u32::BITS,
        ensures
            r.wf(),
    {
        let ghost f = DekoHeapPredicate;
        let heap = DekoHeap::<ORDER>::new(Ghost(f));

        Self(DekoBuddyAllocator::new(heap, Ghost(f)))
    }
}

impl<const ORDER: usize> WellFormed for DekoPageFrameAllocator<ORDER> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.0.wf()
        &&& 0 < ORDER <= u32::BITS
    }
}

/// A type-erased allocator that uses our buddy allocator for serving
/// heap allocations from [`alloc`] crate.
///
/// We do not implement [`core::alloc::Allocator`] directly on
/// [`DekoPageFrameAllocator`] because we want to keep the type information
/// about the order of the buddy allocator separate.
///
/// Consider the following example:
///
/// ```rust,ignore
///  let mut v: alloc::vec::Vec<u8, DekoAllocatorApi> = alloc::vec::Vec::new_in(DekoAllocatorApi);
///  v.push(42);
///
/// let mut v: alloc::vec::Vec<u8, DekoPageFrameAllocator<10>> =
///     alloc::vec::Vec::new_in(DekoPageFrameAllocator::<10>::new()); // this is annoying and expose details about the allocator
/// v.push(42);
/// ```
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoAllocatorApi;

impl WellFormed for DekoAllocatorApi {
    open spec fn wf(&self) -> bool {
        true
    }
}

/// The heap allocator API that uses the global frame allocator.
///
/// Note that in stage2 we do not use any of the heap so this operation
/// relies on the full frame allocator.
#[verifier::external]
unsafe impl core::alloc::Allocator for DekoAllocatorApi {
    #[inline]
    fn allocate(&self, layout: core::alloc::Layout) -> Result<
        core::ptr::NonNull<[u8]>,
        core::alloc::AllocError,
    > {
        if is_stage2() {
            DEKO_FRAME_ALLOCATOR.0.allocate(layout)
        } else {
            DEKO_FRAME_ALLOCATOR_FULL.0.allocate(layout)
        }
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: core::alloc::Layout) {
        if is_stage2() {
            DEKO_FRAME_ALLOCATOR.0.deallocate(ptr, layout)
        } else {
            DEKO_FRAME_ALLOCATOR_FULL.0.deallocate(ptr, layout)
        }
    }
}

} // verus!
