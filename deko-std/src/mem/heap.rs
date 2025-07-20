use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power::*;
use vstd::prelude::*;

use crate::prelude::*;

verus! {

pub const HEAP_ALIGNMENT: u64 = 0x1000;

/// This function checks if the given parameters for a heap are valid only used for
/// initialization functions.
#[verifier::inline]
pub open spec fn valid_heap_param(heap_base: u64, heap_size: u64, order: u64) -> bool {
    let min_block_size = heap_size >> ((order - 1) as u64);

    &&& heap_base > 0
    &&& heap_size > 0
    &&& heap_size >= min_block_size
    &&& min_block_size >= core::mem::size_of::<Node<()>>() as u64
    &&& heap_size % HEAP_ALIGNMENT == 0
    &&& is_power_of_two(heap_size)
    &&& heap_size >= pow(2, order as nat) as u64
}

// 4 KiB
/// The size of a block of a given order.
#[verifier::inline]
pub open spec fn block_size(order: nat) -> nat {
    pow(2, order) as nat
}

#[verifier::inline]
pub open spec fn addr_is_valid_for_order(addr: nat, order: nat) -> bool {
    addr % block_size(order) == 0
}

#[verifier::inline]
pub open spec fn is_power_of_two(n: u64) -> bool {
    n > 0 && (n & (n - 1) as u64) == 0
}

/// Checks if two blocks of memory overlap.
pub open spec fn overlaps_with(left: nat, right: nat, block_size: nat) -> bool {
    let left_end = left + block_size;
    let right_end = right + block_size;
    !(left >= right_end || right >= left_end)
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
        &&& self.block_no_overlapping()
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
    /// The size of the blocks we allocate for a given order.
    pub closed spec fn order_size(&self, order: nat) -> nat {
        block_size(order + log(2, self.min_block_size as int) as nat)
    }

    pub closed spec fn in_heap_range(&self, addr: u64, size: u64) -> bool {
        self.heap_base <= addr && addr + size <= self.heap_base + self.heap_size
    }

    pub closed spec fn block_no_overlapping_at(&self, order: int) -> bool {
        let list = self.free_list@.index(order);
        let block_size = self.order_size(order as nat) as usize;

        // Ensures any block is aligned to the block size.
        &&& forall|i: int|
            0 <= i < list.inner@.ptrs.len() ==> #[trigger] list.inner@.ptrs.index(i).addr()
                % block_size
                == 0
            // Ensures any two blocks cannot overlap.
        &&& forall|i, j: int|
            0 <= i < list.inner@.ptrs.len() && 0 <= j < list.inner@.ptrs.len() && i != j
                ==> !overlaps_with(
                #[trigger] list.inner@.ptrs.index(i).addr() as nat,
                #[trigger] list.inner@.ptrs.index(j).addr() as nat,
                block_size as nat,
            )
    }

    /// Ensures that allocating the same memory twice that causes double use problems.
    pub closed spec fn block_no_overlapping(&self) -> bool {
        forall|i: int| 0 <= i < self.free_list@.len() ==> #[trigger] self.block_no_overlapping_at(i)
    }

    pub closed spec fn heap_size_valid(&self) -> bool {
        // The heap size must be a multiple of the minimum block size.
        &&& self.heap_size % self.min_block_size
            == 0
        // The heap size must be a power of two.
        &&& exists|n: u64|
            {
                &&& #[trigger] pow(2, n as nat) == self.heap_size as nat
                &&& self.min_block_size as nat == pow(2, (n - ORDER + 1) as nat)
                &&& n >= ORDER - 1
            }
            // The heap must be aligned to page size.
        &&& self.heap_size % HEAP_ALIGNMENT
            == 0
        // The heap size must be large enough to hold at least one block of the minimum size.
        &&& self.heap_size >= self.min_block_size >= core::mem::size_of::<Node<u64>>() > 0
    }

    pub closed spec fn is_init(&self) -> bool {
        &&& self.heap_base != 0
        &&& self.heap_size != 0
        &&& self.empty_free_list()
    }

    pub closed spec fn init_ok(&self) -> bool {
        &&& self.is_init()
        &&& forall|i: int|
            #![trigger self.free_list@.index(i)]
            if i == ORDER - 1 as int {
                // This is because we will insert the entire initial block into the last
                // free list.
                self.free_list@.index(i)@.len() == 1
            } else {
                self.free_list@.index(i)@.len() == 0
            }
    }

    pub closed spec fn empty_free_list(&self) -> bool {
        forall|i: int|
            0 <= i < self.free_list@.len() as int ==> #[trigger] self.free_list@.index(
                i,
            ).inner@.ptrs.len() == 0
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
    pub fn init(&mut self, heap_start: u64, heap_size: u64)
        requires
            !old(self).is_init(),
            old(self).wf(),
            valid_heap_param(heap_start, heap_size, ORDER as u64),
        ensures
            self.wf(),
            self.init_ok(),
    {
        self.heap_base = heap_start;

        proof {
            assert(old(self).free_list === self.free_list);
            assert(self.free_list_valid());
        }

        unsafe {
            self.init_unchecked(heap_start, heap_size);
        }
    }

    unsafe fn init_unchecked(&mut self, heap_start: u64, heap_size: u64)
        requires
            !old(self).is_init(),
            old(self).wf(),
            valid_heap_param(heap_start, heap_size, ORDER as u64),
        ensures
            self.wf(),
            self.init_ok(),
    {
        // Since we do not have a method to modify the value in place, we need to
        // manually replace the target list in the free_list with an empty one,
        // update the node, and then "give back" to the free list.
        let top_order = ORDER - 1;
        proof {
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

        self.heap_base = heap_start;
        self.heap_size = heap_size;
        self.min_block_size = heap_size >> (top_order as u64);
    }

    /// Creates a new, _empty_ heap.
    ///
    /// Because Array owns the opauqe [T; N] and we use const array-fill expression,
    /// verus cannot reason anything about it so we just mark this function as trusted.
    #[verifier::external_body]
    pub const fn new(Ghost(f): Ghost<DekoHeapPredicate::<DekoHeap<ORDER>>>) -> (s: Self)
        requires
    // We need ORDER > 0 to have at least one block size.

            0 < ORDER <= 32,
        ensures
            s.wf(),
            f.inv(s),
            !s.is_init(),
    {
        Self {
            free_list: Array::new([const { LinkedList::new() };ORDER]),
            heap_base: 0x0,
            // The total size is determined by the largest possible block.
            heap_size: 0x0,
            // With this geometry, the smallest block is size 1.
            min_block_size: 0x0,
        }
    }

    pub closed spec fn allocation_size_spec(&self, size: u64, align: u64) -> u64 {
        let new_size = if align > size {
            align
        } else {
            size
        };
        let new_size = vstd::math::max(new_size as int, self.min_block_size as int) as u64;

        next_power_of_two_spec(new_size as nat) as u64
    }

    pub closed spec fn valid_size_and_align(&self, size: u64, align: u64) -> bool {
        let new_size = self.allocation_size_spec(size, align);

        &&& align
            <= HEAP_ALIGNMENT  // align must be a power of two and at most the page size.
        &&& is_power_of_two(align)
        &&& new_size <= self.heap_size
        &&& size > 0
    }

    fn allocation_size(&self, mut size: u64, align: u64) -> (s: u64)
        requires
            self.valid_size_and_align(size, align),
        ensures
            s == self.allocation_size_spec(size, align),
            is_power_of_two_spec(s as nat),
            self.min_block_size <= s <= self.heap_size,
    {
        if align > size {
            size = align;
        }
        let size = if size < self.min_block_size {
            self.min_block_size
        } else {
            size
        };

        size.next_power_of_two()
    }

    /// The "order" of an allocation is how many times we need to double
    /// `min_block_size` in order to get a large enough block, as well as
    /// the index we use into `free_lists`.
    #[inline]
    fn allocation_order(&self, size: u64, align: u64) -> (r: u64)
        requires
            self.valid_size_and_align(size, align),
            self.wf(),
        ensures
            0 <= r < ORDER as u64,
    {
        let size = self.allocation_size(size, align);
        // we now have size >= min_block_size.
        let res = size.ilog2();
        let min_block_size_log2 = self.min_block_size.ilog2();

        proof {
            // Recover the exponents for the heap and the size to better
            // assist us in the log reasnoning.
            let exp_heap = choose|exp_heap: nat| #[trigger]
                pow(2, exp_heap) == self.heap_size as nat && self.min_block_size as nat == pow(
                    2,
                    (exp_heap - ORDER + 1) as nat,
                ) && exp_heap >= ORDER - 1;
            let exp_size = choose|exp_size: nat| #[trigger] pow(2, exp_size) == size;

            assert(min_block_size_log2 as nat == exp_heap - ORDER + 1) by {
                lemma_log_pow(2, (exp_heap - ORDER + 1) as nat);
            }
            assert(exp_size == res) by {
                lemma_log_pow(2, exp_size as nat);
            }

            // now we need to show that
            // 0 <= exp_size - (exp_heap - ORDER + 1) < ORDER
            //      1. left side:
            assert(exp_size >= exp_heap - ORDER + 1) by {
                // note that s.0 == size >= self.min_block_size
                lemma_log_is_ordered(2, self.min_block_size as int, size as int);
                // Then we cancel the pow in log.
                lemma_log_pow(2, (exp_heap - ORDER + 1) as nat);
                lemma_log_pow(2, exp_size as nat);
            }
            //      2. right side: exp_size < exp_heap + 1 <= exp_sie <= exp_heap.
            assert(exp_size - (exp_heap - ORDER + 1) < ORDER) by {
                // first note that
                assert(size <= self.heap_size);
                // then we apply the log lemma.
                lemma_log_is_ordered(2, size as int, self.heap_size as int);
                // then we cancel both side.
                lemma_log_pow(2, exp_size as nat);
                lemma_log_pow(2, exp_heap as nat);
            }
        }

        res as u64 - min_block_size_log2 as u64
    }

    /// Allocates a block of memory from the heap.
    ///
    /// TODO: The return type should be a pointer and its permission??
    // #[verifier::external_body]
    pub fn allocate(&mut self, size: u64, align: u64) -> (pt: u64)
        requires
            old(self).wf(),
            old(self).is_init(),
            old(self).valid_size_and_align(size, align),
        ensures
            self.wf(),
            self.in_heap_range(pt, size),
    {
        // Get the order we will need.
        let order_needed = self.allocation_order(size, align) as usize;

        let mut order = order_needed;
        let len = self.free_list.len();
        // Start with the smallest acceptable block size, and search
        // upwards until we reach blocks the size of the entire heap.
        while order < len
            invariant
                self.wf(),
                order <= len,
                order_needed <= order,
                len == self.free_list@.len(),
            decreases len - order,
        {
            // Do we have a block of this size? Check head.
            if !self.free_list.index(order).head.is_none() {
                assert(!self.free_list@.index(order as int).is_empty());
                // Let's pop out the first block.
            }
            // todo!()

            order += 1;
        }

        1
    }
}

impl<const ORDER: usize> WellFormed for DekoHeap<ORDER> {
    closed spec fn wf(&self) -> bool {
        &&& self.heap_size_valid() && self.is_init()
        &&& self.free_list_valid()
        &&& self.free_list@.len() == ORDER as int
        &&& ORDER - 1 >= 0
    }
}

} // verus!
