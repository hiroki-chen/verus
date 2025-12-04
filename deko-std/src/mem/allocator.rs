use core::marker::PhantomData;

use vstd::layout::valid_layout;
use vstd::raw_ptr::{Dealloc, DeallocData, IsExposed, PointsToRaw, Provenance};
use vstd::simple_pptr::{MemContents, PPtr};

use crate::boxed::Box;
use crate::prelude::*;

verus! {

/// The adapter that allows using `DekoHeap` as an allocator.
#[verifier::external]
unsafe impl<V: WellFormed + Heap> core::alloc::Allocator for DekoBuddyAllocator<V> {
    fn allocate(&self, layout: core::alloc::Layout) -> Result<
        core::ptr::NonNull<[u8]>,
        core::alloc::AllocError,
    > {
        match self.alloc_impl(layout.size(), layout.align()) {
            ptr if ptr != 0 => {
                let slice_ptr = core::ptr::slice_from_raw_parts_mut(ptr as *mut u8, layout.size());
                core::ptr::NonNull::new(slice_ptr).ok_or(core::alloc::AllocError)
            },
            _ => Err(core::alloc::AllocError),
        }
    }

    unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: core::alloc::Layout) {
        self.dealloc_impl(ptr.as_ptr(), layout.size(), layout.align());
    }
}

/// The default heap size configuration for the Deko memory allocator.
///
/// This constant defines the size parameter for the buddy allocator's heap management.
/// The value represents the number of allocation units or blocks that the heap can manage,
/// not the direct byte size of the heap.
///
/// # Usage
///
/// This constant is used as a type parameter for [`DekoHeap<HEAP_SIZE>`] and affects:
/// - The number of allocation blocks the buddy allocator can track
/// - The internal data structures size for heap management
/// - The maximum number of concurrent allocations
///
/// # Examples
///
/// ```rust
/// // Used in the default heap allocator type
/// type DefaultDekoHeapAllocator = DekoBuddyAllocator<DekoHeap<HEAP_SIZE>>;
///
/// // Used during heap initialization
/// allocator.init(heap_start, heap_size, HEAP_SIZE as u64);
/// ```
///
/// # Notes
///
/// - This is a compile-time constant that affects the heap allocator's capacity
/// - The actual heap memory size is determined at runtime during initialization
/// - Increasing this value allows more concurrent allocations but uses more metadata space
/// - Must be coordinated with the `valid_heap_param` function requirements
///
/// # See Also
///
/// - [`DekoBuddyAllocator`] - The main heap allocator that uses this constant
/// - [`DekoHeap`] - The heap implementation parameterized by this size
/// - [`valid_heap_param`] - Function that validates heap parameters including this size
pub const HEAP_SIZE: usize = 10;

/// The _true_ global allocator for Deko that manages the physical pages.
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
pub struct DekoBuddyAllocator<V: WellFormed + Heap> {
    /// The allocator that manages the heap.
    ///
    /// This is a RwLock to allow concurrent access to the heap.
    /// Note that this is not a global allocator, so we do not use
    /// the `GlobalAlloc` trait.
    allocator: DekoRwLock<V, (), DekoHeapPredicate>,
}

impl<V: WellFormed + Heap> DekoBuddyAllocator<V> {
    /// Creates a new `DekoHeapAllocator` with the given heap.
    ///
    /// The caller must ensure that the heap is properly initialized and
    /// the memory is mapped.
    pub const fn new(v: V, Ghost(pred): Ghost<DekoHeapPredicate>) -> (s: Self)
        requires
            v.wf(),
            pred.deep_inv(v),
        ensures
            s.wf(),
    {
        Self { allocator: DekoRwLock::new(DekoAtomicData::new(v), (), Ghost(pred)) }
    }

    pub fn init(&self, heap_start: u64, heap_size: u64)
        requires
            self.wf(),
            crate::heap::valid_heap_param(heap_start, heap_size, HEAP_SIZE as u64),
    {
        let (mut allocator, write_handle) = self.allocator.acquire_write();

        // If already initialized, we do nothing.
        if allocator.data.is_init_impl() {
            write_handle.release_write(allocator);
            return ;
        }
        allocator.data.init(heap_start, heap_size, HEAP_SIZE as u64);

        write_handle.release_write(allocator);
    }

    /// This API is *hidden* because we do not want the caller to manipulate any
    /// raw pointers and deallocations directly.
    #[verifier::external_body]
    #[inline(always)]
    pub fn alloc(&self, size: usize, align: usize) -> (pt: (
        *mut u8,
        Tracked<PointsToRaw>,
        Tracked<Dealloc>,
    ))
        requires
            self.wf(),
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
        let p = self.alloc_impl(size, align) as *mut u8;

        unsafe {
            core::ptr::write_bytes(p, 0, size);
        }

        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn dealloc(
        &self,
        ptr: *mut u8,
        size: usize,
        align: usize,
        Tracked(perm): Tracked<PointsToRaw>,
        Tracked(dealloc): Tracked<Dealloc>,
    )
        requires
            self.wf(),
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

    fn alloc_impl(&self, size: usize, align: usize) -> (r: u64)
        requires
            self.wf(),
    {
        let (mut allocator, write_handle) = self.allocator.acquire_write();

        if allocator.data.check_allocation_size(size as u64, align as u64) {
            let res = allocator.data.allocate(size as u64, align as u64);
            write_handle.release_write(allocator);
            res
        } else {
            write_handle.release_write(allocator);

            // Error.
            0
        }
    }

    fn dealloc_impl(&self, ptr: *mut u8, size: usize, align: usize)
        requires
            self.wf(),
    {
        let (mut allocator, write_handle) = self.allocator.acquire_write();

        if allocator.data.check_allocation_size(size as u64, align as u64) {
            // TODO: Since the allocator itself is globally shared and protected
            // by the RwLock, we need to find a way to reason about the safety
            // issue here to guarantee that the pointer is indeed allocated from
            // this allocator.
            //
            // Perhaps we will need to have a tracked registry of all allocated
            // pointers from this allocator like a `tracked` meta allocator.
            assume(allocator.data.in_heap_range(ptr.addr() as nat, size as nat));

            allocator.data.deallocate(ptr.addr() as u64, size as u64, align as u64);
            write_handle.release_write(allocator);
            return ;
        } else {
            write_handle.release_write(allocator);
        }
    }
}

impl<V: WellFormed + Heap> WellFormed for DekoBuddyAllocator<V> {
    closed spec fn wf(&self) -> bool {
        true
    }
}

/// Please be aware that this is NOT:
/// - the global allocator for Rust.
/// - the virtual heap allocator, and
///
/// this IS
/// - the physical memory allocator that allocates physical pages.
pub type DefaultDekoHeapAllocator = DekoBuddyAllocator<DekoHeap<HEAP_SIZE>>;

} // verus!
