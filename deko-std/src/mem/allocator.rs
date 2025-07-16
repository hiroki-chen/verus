use core::marker::PhantomData;

use vstd::layout::valid_layout;
use vstd::raw_ptr::{Dealloc, DeallocData, IsExposed, PointsToRaw, Provenance};
use vstd::simple_pptr::{MemContents, PPtr};

use crate::boxed::Box;
use crate::prelude::*;

verus! {

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
    /// The memory region is a normal memory region.
    Normal,
    // In case we need more.
}

pub struct MemoryManagerPredicate;

impl Predicate<DekoMemoryManager> for MemoryManagerPredicate {
    open spec fn inv(self, mm: DekoMemoryManager) -> bool {
        true
    }
}

/// An abstraction over a _slice_ of memories on the physical machine.
///
/// This provides good abstraction over the memory owned by the L2 VM.
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
///
/// This allocator uses the buddy system allocation algorithm to manage the heap. We assume the heap
/// is a large contigunous memory already mapped by the monitor. Basically this is just a wrapper
/// around the `DekoHeap` type.
#[verifier::reject_recursive_types(V)]
pub struct DekoHeapAllocator<V, F> where V: WellFormed + Heap, F: Predicate<V> {
    /// The allocator that manages the heap.
    ///
    /// This is a mutex to allow concurrent access to the heap.
    /// Note that this is not a global allocator, so we do not use
    /// the `GlobalAlloc` trait.
    allocator: Mutex<V, F>,
}

/// A global allocator that is used to allocate memory for the monitor.
pub exec static DEKO_ALLOCATOR: DekoHeapAllocator<
    DekoHeap<HEAP_SIZE>,
    DekoHeapPredicate<DekoHeap<HEAP_SIZE>>,
>
    ensures
        DEKO_ALLOCATOR.wf(),
{
    let ghost f = DekoHeapPredicate::<DekoHeap<HEAP_SIZE>>(core::marker::PhantomData);
    let heap = DekoHeap::<HEAP_SIZE>::new(16, Ghost(f));

    DekoHeapAllocator::new(heap, Ghost(f))
}

impl<V, F> DekoHeapAllocator<V, F> where V: WellFormed + Heap, F: Predicate<V> {
    /// Creates a new `DekoHeapAllocator` with the given heap.
    ///
    /// The caller must ensure that the heap is properly initialized and
    /// the memory is mapped.
    pub const fn new(v: V, Ghost(pred): Ghost<F>) -> (s: Self)
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
    #[inline(always)]
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
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[verifier::external_body]
    #[inline(always)]
    pub(crate) fn dealloc(
        &self,
        ptr: *mut u8,
        size: usize,
        align: usize,
        Tracked(perm): Tracked<PointsToRaw>,
        Tracked(dealloc): Tracked<Dealloc>,
    )
        requires
            size != 0,
            dealloc.addr() == ptr.addr(),
            dealloc.size() == size as nat,
            dealloc.align() == align as nat,
            ptr@.provenance == perm.provenance(),
            perm.is_range(ptr.addr() as int, size as int),
        opens_invariants none
    {
        self.dealloc_impl(ptr, size, align);
    }

    fn alloc_impl(&self, size: usize, align: usize) -> *mut u8 {
        core::ptr::null_mut()  // TODO: Implement the actual allocation logic.

    }

    fn dealloc_impl(&self, ptr: *mut u8, size: usize, align: usize) {
    }
}

impl<V, F> WellFormed for DekoHeapAllocator<V, F> where V: WellFormed + Heap, F: Predicate<V> {
    closed spec fn wf(&self) -> bool {
        self.allocator.wf()
    }
}

pub type DefaultDekoHeapAllocator = DekoHeapAllocator<
    DekoHeap<HEAP_SIZE>,
    DekoHeapPredicate<DekoHeap<HEAP_SIZE>>,
>;

} // verus!
