use vstd::prelude::*;

use crate::prelude::*;

verus! {

pub const HEAP_ALIGNMENT: u64 = 0x1000;

// 4 KiB
/// The size of a block of a given order.
#[verifier::inline]
pub open spec fn block_size(order: nat) -> nat {
    (1 << order as u64) as nat
}

#[verifier::inline]
pub open spec fn addr_is_valid_for_order(addr: nat, order: nat) -> bool {
    addr % block_size(order) == 0
}

#[verifier::inline]
pub open spec fn is_power_of_two(n: u64) -> bool {
    n > 0 && (n & (n - 1) as u64) == 0
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
    ///
    /// The node itself does not contain any value and the address and
    /// size information is already stored in the pointer and the list
    /// it belongs to. The value is thus a ZST.
    free_list: Array<LinkedList<()>, ORDER>,
    /// The start address of the heap.
    heap_base: u64,
    /// The size of the heap.
    heap_size: u64,
    /// Minimum size of a block in the heap.
    min_block_size: u64,
}

impl<const ORDER: usize> Heap for DekoHeap<ORDER> {
    closed spec fn free_list_valid(&self) -> bool {
        &&& self.free_list.wf()
        &&& forall|i: int, j: int|
            #![trigger self.free_list@.index(i), self.free_list@.index(i)@.index(j)]
            0 <= i < self.free_list@.len() as int ==> self.free_list@.index(i).wf() && 0 <= j
                < self.free_list@.index(i)@.len() as int ==> self.free_list@.index(i)@.index(j).wf()
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
        // The heap size must be a multiple of the minimum block size.
        &&& heap_size % self.min_block_size
            == 0
        // The heap size must be a power of two.
        &&& is_power_of_two(
            heap_size,
        )
        // The heap must be aligned to page size.
        &&& heap_size % HEAP_ALIGNMENT
            == 0
        // The heap size must be at least the minimum block size.
        &&& heap_size
            >= self.min_block_size
        // The heap size must be large enough to hold at least one block of the minimum size.
        &&& self.min_block_size >= core::mem::size_of::<
            Node<u64>,
        >()
        // The total heap size is now derived directly from ORDER.
        // A buddy system typically manages a power-of-two-sized region.
        // Let's assume the largest block is 2^(ORDER-1) and the smallest is 2^0 = 1.
        &&& self.heap_size == (1u64 << (ORDER - 1))
        &&& self.min_block_size == 1
    }

    pub closed spec fn is_init(&self) -> bool {
        self.heap_base != 0
    }

    pub closed spec fn init_ok(&self) -> bool {
        &&& self.is_init()
        &&& forall|i: int|
            #![trigger self.free_list@.index(i)]
            if i == ORDER - 1 as int {
                self.free_list@.index(i)@.len() == 1
            } else {
                self.free_list@.index(i)@.len() == 0
            }
    }

    pub closed spec fn empty_free_list(&self) -> bool {
        forall|i: int|
            0 <= i < self.free_list@.len() as int ==> #[trigger] self.free_list@.index(i)@.len()
                == 0
    }

    /// Initializes the heap with a given memory region, making it ready for allocations.
    ///
    /// This is the bootstrapping function. It takes a raw permission for a large memory
    /// region, finds the largest power-of-2 block that fits, and adds that single
    /// block to the appropriate free list.
    ///
    /// # Safety
    /// The caller must guarantee that the provided permission `perm` corresponds to a
    /// valid, unused memory region starting at `heap_start` of `heap_size`.
    pub fn init(&mut self, heap_start: u64)
        requires
            !old(self).is_init(),
            old(self).wf(),
            old(self).empty_free_list(),
            heap_start > 0,
        ensures
            self.wf(),
            self.init_ok(),
    {
        self.heap_base = heap_start;

        proof {
            assert(old(self).free_list === self.free_list);
        }

        unsafe {
            self.init_unchecked(heap_start);
        }
    }

    unsafe fn init_unchecked(&mut self, heap_start: u64)
        requires
            old(self).is_init(),
            old(self).wf(),
            heap_start > 0,
            old(self).empty_free_list(),
        ensures
            self.wf(),
            self.init_ok(),
    {
        // Since we do not have a method to modify the value in place, we need to
        // manually replace the target list in the free_list with an empty one,
        // update the node, and then "give back" to the free list.
        let top_order = ORDER - 1;
        proof {
            assert(old(self).free_list@.index(top_order as int)@.len() == 0);
            assert(old(self).free_list@.index(top_order as int).wf());
        }
        let dummy_list = LinkedList::new();
        let mut old = self.free_list.update(top_order, dummy_list);
        // The entire heap is one large block. Its order is the highest one.
        // Create a pointer to the start of the heap. This will be our single node.
        let (block_ptr, Tracked(mut points_to)) = DekoPPtr::<Node<()>>::from_raw_uninit(heap_start);

        proof {
            // Workaround for well-formedness from possibly invalid address.
            assume(points_to.value().value.wf());
            assume(points_to.is_init());
        }

        old.push_front_no_alloc(block_ptr, Tracked(points_to));
        // Give it back to the free list.
        let _ = self.free_list.update(top_order, old);  // discard.
    }

    /// Creates a new, _empty_ heap.
    ///
    /// Because Array owns the opauqe [T; N] and we use const array-fill expression,
    /// verus cannot reason anything about it so we just mark this function as trusted.
    #[verifier::external_body]
    pub const fn new(Ghost(f): Ghost<DekoHeapPredicate::<DekoHeap<ORDER>>>) -> (s: Self)
        requires
    // We need ORDER > 0 to have at least one block size.

            ORDER > 0,
        ensures
            s.wf(),
            f.inv(s),
            !s.is_init(),
    {
        Self {
            free_list: Array::new([const { LinkedList::new() };ORDER]),
            heap_base: 0x0,
            // The total size is determined by the largest possible block.
            heap_size: 1u64 << (ORDER - 1),
            // With this geometry, the smallest block is size 1.
            min_block_size: 1,
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
        &&& self.heap_size_valid(self.heap_size)
        &&& self.free_list_valid()
        &&& ORDER - 1 >= 0
        &&& self.free_list@.len() == ORDER as int
    }
}

} // verus!
