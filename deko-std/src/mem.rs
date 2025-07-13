use vstd::prelude::*;

verus! {

/// A tracked enum for tracking the read/write permission on a given piece of memory.
///
/// TODO: Design privilege.
pub enum PermissionDekoMem {
    Foo,
}

impl PermissionDekoMem {
    /// Check if the permission is well-formed.
    pub open spec fn wf(&self) -> bool {
        true
        // TODO: Implement me!

    }
}

} // verus!
#[cfg(feature = "alloc")]
verus! {

use crate::prelude::*;
use vstd::layout::valid_layout;
use vstd::raw_ptr::{Dealloc, DeallocData, PointsToRaw, Provenance, IsExposed};
use core::marker::PhantomData;
use vstd::simple_pptr::{PPtr, MemContents};

pub struct AllocatorPredicate;

impl<V: WellFormed + Heap> Predicate<V> for AllocatorPredicate {
    closed spec fn inv(self, v: V) -> bool {
        true
    }
}

/// The _true_ global allocator for Deko.
///
/// For safety reasons we explicitly disallow _any_ attempt to use the default
/// global allocator in Rust because:
///
/// - They are proxy functions that finally re-direct to our implementation but
///   there might be more unsafe operations that bloat the TCB.
/// - They are implicit and may create accidental _raw_ pointer usages that Verus
///   has not created permissioned tokens for.
///
/// We equip every heap-allocated objects with the API that requires the caller
/// to prepare for a `DekoAllocator` instance that is used to allocate memory
/// and deallocate memory. It is idiomatic to just declare it as a Lazy or static
/// object in the root of the crate:
///
/// ```rust
///     pub exec static ALLOC: DekoAllocator = DekoAllocator::new();
///     pub exec static ALLOCATOR: Lazy<DekoAllocator> = Lazy::new(|| DekoAllocator::new());
/// ```
#[verifier::reject_recursive_types(V)]
pub struct DekoAllocator<V: WellFormed + Heap> {
    allocator: Mutex<V, AllocatorPredicate>,
}

pub trait Heap {

}
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

/// A global allocator that is used to allocate memory for the monitor.
pub exec static DEKO_ALLOCATOR: DekoAllocator<DekoHeap<12>>
    ensures
        DEKO_ALLOCATOR.wf(),
{
    DekoAllocator::new(DekoHeap::<12>::new(), Ghost(AllocatorPredicate {  }))
}

impl<V: WellFormed + Heap> DekoAllocator<V> {
    pub const fn new(v: V, Ghost(pred): Ghost<AllocatorPredicate>) -> (s: Self)
        requires
            v.wf(),
            pred.inv(v),
        ensures
            s.wf(),
    {
        Self { allocator: Mutex::new(v, Ghost(pred)) }
    }

    /// This API is *hidden* because we do not want the caller to manipulate any
    /// raw pointers and deallocations directly.
    #[verifier::external_body]
    pub(crate) fn alloc(&self, size: usize, align: usize) -> (pt: (
        *mut u8,
        Tracked<PointsToRaw>,
        Tracked<Dealloc>,
    ))
        requires
            valid_layout(size, align),
            size != 0,
        ensures
            pt.1@.is_range(pt.0.addr() as int, size as int),
            pt.2@@ == (DeallocData {
                addr: pt.0.addr(),
                size: size as nat,
                align: align as nat,
                provenance: pt.1@.provenance(),
            }),
            pt.0.addr() as int % align as int == 0,
            pt.0@.provenance == pt.1@.provenance(),
        opens_invariants none
    {
        let p = self.alloc_impl(size, align);
        if p.is_null() {
            panic!("DekoAllocator::alloc: allocation failed");
        }
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[verifier::external_body]
    fn alloc_impl(&self, size: usize, align: usize) -> *mut u8 {
        todo!()
    }
}

impl<A: WellFormed + Heap> WellFormed for DekoAllocator<A> {
    closed spec fn wf(&self) -> bool {
        self.allocator.wf()
    }
}

struct Allocator;

#[verifier::external]
unsafe impl core::alloc::GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        todo!()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        todo!()
    }
}

/// We do not use Rust's global allocator by default so this is just a dummy one.
/// Any use of the global allocator will panic.
#[verifier::external]
#[global_allocator]
static __DISCARD: Allocator = Allocator;

} // verus!
