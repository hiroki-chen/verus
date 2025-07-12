//! Abstraction over a heap system.
use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

/// A heap that uses buddy system with configurable order.
///
/// Before using this heap make sure that the system's memory is
/// properly initialized, paging is enabled, etc.
/// 
/// `ORDER` is the order of the heap, which is the base-2 logarithm of the
/// size of the heap. Note that the maximum block size is exactly one byte smaller!
/// For example, if `ORDER` is 12, then the heap size is 2^12 - 1 = 4095 bytes (~4 KiB). 
/// 
/// # Examples
/// 
/// ```rust
/// use deko_core::allocator::heap::DekoHeap;
/// 
/// static mut BUF: [u8; 4096] = [0; 4096];
/// 
/// let heap = DekoHeap::<12>::new(BUF.as_mut_ptr() as usize, BUF.len());
/// let allocator = deko_std::allocator::DekoAllocator::new(heap);
/// ```
/// 
/// # References
/// 
/// - rcore-os/buddy_system_allocator
pub struct DekoHeap<const ORDER: usize> {}

impl<const ORDER: usize> Heap for DekoHeap<ORDER> {

}

impl<const ORDER: usize> DekoHeap<ORDER> {
    /// Creates a new heap.
    pub const fn new() -> (s: Self)
        ensures 
            s.wf(),
    {
        Self {  }
    }
}

impl<const ORDER: usize> WellFormed for DekoHeap<ORDER> {
    closed spec fn wf(&self) -> bool {
        true
    }
}

} // verus!
