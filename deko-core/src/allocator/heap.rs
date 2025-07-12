//! Abstraction over a heap system.
use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

/// A heap that uses buddy system with configurable order.
///
/// Reference: rcore-os/buddy_system_allocator
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
