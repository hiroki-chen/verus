//! This crate implements the memory management for the Deko monitor.
//!
//! We illustrate the memory hierarchy as follows:
//!
//  ┌──────────────────────────────────┐
//  │                                  │
//  │                                  │
//  │          User-Level MM           │
//  │                                  │
//  │                                  │
//  └───────┬───────────────────┬──────┘
//          │                   │
//          │                   │
//  ┌───────▼──────┐    ┌───────▼──────┐
//  │              │    │              │
//  │   Deko Mem   │    │   Deko Mem   │
//  │              │    │              │
//  ├──────────────┤    ├──────────────┤
//  │              │    │              │
//  │      MM      │    │      MM      │
//  │              │    │              │
//  └──────┬───────┘    └───────┬──────┘
//         │                    │
//         │                    │
//         │                    │
//         ▼                    │
//  ┌───────────────────────────▼───────┐
//  │                                   │
//  │                                   │
//  │           Heap (system)           │
//  │                                   │
//  │                                   │
//  └───────────────────────────────────┘
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

use crate::boxed::Box;
use crate::prelude::*;
use vstd::layout::valid_layout;
use vstd::raw_ptr::{Dealloc, DeallocData, PointsToRaw, Provenance, IsExposed};
use core::marker::PhantomData;
use vstd::simple_pptr::{PPtr, MemContents};

pub const PAGE_SIZE: u64 = 0x1000;

// 4096 bytes
pub const PAGE_MASK: u64 = !(PAGE_SIZE - 1);

// 0xFFFFF000
/// A trait to describe the memory manager.
pub trait MemoryManager: WellFormed {
    /// Allocates a region of memory from the memory manager's managed page table.
    fn map();

    /// Unmap a region of memory from the memory manager's managed page table.
    fn unmap();

    /// Handles a page fault.
    fn page_fault(&self);
}

/// Deko's memory manager object that manages the memory regions and page tables.
/// This is only used to manage the memory for low-privileged Linux kernel.
pub struct DekoMemoryManager {
    /// A list of memories managed by this memory manager equivalent to
    /// `free_list` in the Linux kernel.
    memories: (),
    /// The page table backend for this memory manager.
    page_table: (),
    /// The heap ending point.
    heap_end: Option<u64>,
}

pub enum MemoryRegionType {
    Heap,
    Stack,
    Elf,
    Reserved,
}

pub struct MemoryManagerPredicate;

impl Predicate<DekoMemoryManager> for MemoryManagerPredicate {
    open spec fn inv(self, mm: DekoMemoryManager) -> bool {
        true
    }
}

/// An abstraction over a _slice_ of memories on the physical machine.
#[verifier::reject_recursive_types(MM)]
pub struct DekoMemory<MM: MemoryManager> {
    /// The start address of the memory region. (virtual)
    range: (u64, u64),
    /// manager for this memory region. You can think of it as a
    /// memory callback that is used to allocate and deallocate memory.
    ///
    /// We do not apply an explicit lock on this allocator.
    mamanger: Box<MM, MemoryManagerPredicate>,
    /// The type of the memory region.
    ty: MemoryRegionType,
}

impl<MM: MemoryManager> View for DekoMemory<MM> {
    type V = (u64, u64);

    closed spec fn view(&self) -> Self::V {
        self.range
    }
}

impl<MM: MemoryManager> DekoMemory<MM> {
    #[verifier::inline]
    pub open spec fn contains(&self, addr: u64) -> bool {
        self@.0 <= addr < self@.1
    }

    #[verifier::inline]
    pub open spec fn subset_of(&self, other: (u64, u64)) -> bool {
        &&& page_start(self@.0) <= page_start(other.0)
        &&& page_start(self@.1) >= page_start(other.1)
    }
}

#[verifier::inline]
pub open spec fn page_start(addr: u64) -> u64 {
    addr & PAGE_MASK
}

/// Tracks whether a holder is having the permission to read/write the memory region.
pub tracked struct PermissionDekoMemoryRegion {}

/// The default of the heap that can we manage.
///
/// 2 ^ 33 - 1 = 17179869183 bytes (~4 GiB).
pub const HEAP_SIZE: usize = 33;

pub struct AllocatorPredicate;

impl<V: WellFormed + Heap> Predicate<V> for AllocatorPredicate {
    closed spec fn inv(self, v: V) -> bool {
        true
    }
}

/// The _true_ global allocator for Deko that manages the heap.
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
/// to prepare for a `DekoHeapAllocator` instance that is used to allocate memory
/// and deallocate memory. It is idiomatic to just declare it as a Lazy or static
/// object in the root of the crate:
///
/// ```rust
///     pub exec static ALLOC: DekoHeapAllocator = DekoHeapAllocator::new();
///     pub exec static ALLOCATOR: Lazy<DekoHeapAllocator> = Lazy::new(|| DekoHeapAllocator::new());
/// ```
#[verifier::reject_recursive_types(V)]
pub struct DekoHeapAllocator<V: WellFormed + Heap> {
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
/// let allocator = deko_std::allocator::DekoHeapAllocator::new(heap);
/// ```
///
/// # References
///
/// - rcore-os/buddy_system_allocator
pub struct DekoHeap<const ORDER: usize> {}

impl<const ORDER: usize> Heap for DekoHeap<ORDER> {

}

impl<const ORDER: usize> DekoHeap<ORDER> {
    /// Creates a new, _empty_ heap.
    pub const fn new() -> (s: Self)
        ensures
            s.wf(),
    {
        Self {  }
    }

    /// Adds a memory region to the heap.
    ///
    /// The memory region must be _owned_ by the monitor (which is trivial as for now),
    /// and the memory region must be well-formed.
    pub fn add_to_heap(&self, mem_region: ()) {
    }
}

impl<const ORDER: usize> WellFormed for DekoHeap<ORDER> {
    closed spec fn wf(&self) -> bool {
        true
    }
}

/// A global allocator that is used to allocate memory for the monitor.
pub exec static DEKO_ALLOCATOR: DekoHeapAllocator<DekoHeap<HEAP_SIZE>>
    ensures
        DEKO_ALLOCATOR.wf(),
{
    DekoHeapAllocator::new(DekoHeap::<HEAP_SIZE>::new(), Ghost(AllocatorPredicate {  }))
}

impl<V: WellFormed + Heap> DekoHeapAllocator<V> {
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
            panic!("DekoHeapAllocator::alloc: allocation failed");
        }
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[verifier::external_body]
    fn alloc_impl(&self, size: usize, align: usize) -> *mut u8 {
        todo!()
    }
}

impl<A: WellFormed + Heap> WellFormed for DekoHeapAllocator<A> {
    closed spec fn wf(&self) -> bool {
        self.allocator.wf()
    }
}

struct Allocator;

#[verifier::external]
unsafe impl core::alloc::GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        panic!("DekoHeapAllocator is not used as the global allocator by default. Use DekoHeapAllocator::alloc instead.");
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        panic!("DekoHeapAllocator is not used as the global allocator by default. Use DekoHeapAllocator::dealloc instead.");
    }
}

/// We do not use Rust's global allocator by default so this is just a dummy one.
/// Any use of the global allocator will panic.
#[verifier::external]
#[global_allocator]
static __DISCARD: Allocator = Allocator;

} // verus!
