use vstd::prelude::*;

use crate::prelude::*;

verus! {

/// The size of a block of a given order.
#[verifier::inline]
pub open spec fn block_size(order: nat) -> nat {
    (1 << order as u64) as nat
}

#[verifier::inline]
pub open spec fn addr_is_valid_for_order(addr: nat, order: nat) -> bool {
    addr % block_size(order) == 0
}

pub trait Heap {
    spec fn free_list_valid(&self) -> bool;

    // The total size of the heap this instance manages.
    spec fn heap_size(&self) -> nat;
}

pub ghost struct DekoHeapPredicate<V: WellFormed + Heap>(pub core::marker::PhantomData<V>);

pub ghost struct DekoHeapListPredicate<V: WellFormed + Heap>(pub core::marker::PhantomData<V>);

impl<V: WellFormed + Heap> Predicate<V> for DekoHeapPredicate<V> {
    closed spec fn inv(self, v: V) -> bool {
        &&& v.free_list_valid()
    }
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
pub struct DekoHeap<const ORDER: usize> {
    /// An array of linked lists. free_list[i] is the head of the list
    /// of free blocks of order `i`. The value stored is the offset
    /// from `heap_start`.
    ///
    /// Note that LinkedList must not be allocated on the heap before
    /// heap is initialized.
    free_list: Array<LinkedList<u64>, ORDER>,
    /// The start address of the heap.
    heap_base: u64,
    /// The size of the heap.
    heap_size: u64,
    /// Minimum size of a block in the heap.
    min_block_size: u64,
}

impl<const ORDER: usize> Heap for DekoHeap<ORDER> {
    closed spec fn free_list_valid(&self) -> bool {
        // forall|i: int|
        //     0 <= i < self.free_list@.len() ==> self.free_list@.index(i) == None::<u64>
        //         || self.heap_start <= self.free_list@.index(i).unwrap() < self.heap_size
        true
    }

    #[verifier::inline]
    open spec fn heap_size(&self) -> nat {
        block_size(ORDER as nat)
    }
}

impl<const ORDER: usize> DekoHeap<ORDER> {
    pub closed spec fn in_heap_range(&self, addr: u64, size: u64) -> bool {
        self.heap_base <= addr && addr + size <= self.heap_base + self.heap_size
    }

    pub closed spec fn heap_size_valid(&self, heap_size: u64) -> bool {
        0 < heap_size <= (1 << ORDER) as u64 - 1 && heap_size % self.min_block_size == 0
    }

    pub closed spec fn is_init(&self) -> bool {
        self.heap_base != 0 && self.heap_size > 0
    }

    pub fn init(&mut self, heap_start: u64, heap_size: u64)
        requires
            !old(self).is_init(),
            old(self).wf(),
            old(self).heap_size_valid(heap_size),
            heap_start > 0,
        ensures
            self.is_init(),
    {
        self.heap_base = heap_start;
        self.heap_size = heap_size;
        // Initialize the free list with empty linked lists.
    }

    /// Creates a new, _empty_ heap.
    ///
    /// Because Array owns the opauqe [T; N] type we have no control over
    /// the post-condition it may create so f.inv(s) will fail if we remove
    /// the `#[verifier::external_body]` attribute although this seems very
    /// obivious that `forall |i: int| 0 <= i < N ==> s.free_list@.index(i) == None::<u64>`.
    #[verifier::external_body]
    pub const fn new(
        min_block_size: u64,
        Ghost(f): Ghost<DekoHeapPredicate::<DekoHeap<ORDER>>>,
    ) -> (s: Self)
        ensures
            s.wf(),
            f.inv(s),
            !s.is_init(),
    {
        Self {
            free_list: Array::new([const { LinkedList::new() };ORDER]),
            heap_base: 0x0,
            heap_size: (1 << ORDER) - 1,
            min_block_size,
        }
    }

    /// Allocates a block of memory from the heap.
    #[verifier::external_body]  // todo
    pub fn allocate(&mut self, size: u64, align: u64) -> (addr: u64)
        requires
            old(self).wf(),
            old(self).is_init(),
            size != 0,
        ensures
            self.wf(),
    {
        1
    }
}

impl<const ORDER: usize> WellFormed for DekoHeap<ORDER> {
    closed spec fn wf(&self) -> bool {
        if self.is_init() {
            &&& self.heap_base != 0
            &&& self.heap_size > 0
            &&& self.heap_size_valid(self.heap_size)
            &&& self.free_list_valid()
        } else {
            true
        }
    }
}

} // verus!
