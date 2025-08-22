use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::prelude::*;

verus! {

/// An alias
pub type DekoHeapBlock = DekoPPtr<Node<()>>;

pub type DekoHeapBlockPerm = DekoPointsTo<Node<()>>;

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

/// A trait that defines the interface for a heap.
///
/// WellFormed -> Heap -> WellFormed this creates a loop.
pub trait Heap: WellFormed + Sized {
    spec fn in_heap_range(&self, addr: nat, size: nat) -> bool;

    spec fn valid_size_and_align(&self, size: u64, align: u64) -> bool;

    spec fn free_list_valid(&self) -> bool;

    fn check_allocation_size(&self, size: u64, align: u64) -> (r: bool)
        ensures
            r <==> self.valid_size_and_align(size, align),
    ;

    fn allocate(&mut self, size: u64, align: u64) -> (pt: u64)
        requires
            old(self).wf(),
            old(self).free_list_valid(),
            old(self).valid_size_and_align(size, align),
        ensures
            self.wf(),
            self.free_list_valid(),
            pt != 0 ==> self.in_heap_range(pt as nat, size as nat),
    ;

    fn deallocate(&mut self, ptr: u64, size: u64, align: u64)
        requires
            old(self).valid_size_and_align(size, align),
            old(self).wf(),
            old(self).free_list_valid(),
            old(self).in_heap_range(ptr as nat, size as nat),
        ensures
            self.wf(),
            self.free_list_valid(),
    ;
}

pub ghost struct DekoHeapPredicate;

impl<V: WellFormed + Heap> RwLockPredicate<V> for DekoHeapPredicate {
    open spec fn inv(self, v: V) -> bool {
        &&& v.wf()
        &&& v.free_list_valid()
    }
}

/// A heap that uses buddy system with configurable order. Note that this struct
/// is completely ignorant of the type of the pointer and just manipulate the
/// raw memory. The retuning value will be used for the `DekoPPtr` type.
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
    closed spec fn valid_size_and_align(&self, size: u64, align: u64) -> bool {
        let new_size = self.allocation_size_spec(size, align);

        &&& align
            <= HEAP_ALIGNMENT  // align must be a power of two and at most the page size.
        &&& is_power_of_two(align)
        &&& new_size <= self.heap_size
        &&& size > 0
    }

    closed spec fn in_heap_range(&self, addr: nat, size: nat) -> bool {
        &&& self.heap_base as nat <= addr
        &&& addr + size <= (self.heap_base + self.heap_size) as nat
    }

    closed spec fn free_list_valid(&self) -> bool {
        &&& self.block_no_overlapping()
        &&& self.free_list.wf()
        &&& forall|i: int|
            0 <= i < self.free_list@.len() ==> #[trigger] self.free_list@.index(i).wf()
    }

    fn check_allocation_size(&self, mut size: u64, align: u64) -> (r: bool)
        ensures
            r <==> self.valid_size_and_align(size, align),
    {
        if size == 0 {
            return false;
        }
        if align > size {
            size = align;
        }
        let size = if size <= self.min_block_size {
            self.min_block_size
        } else {
            size
        };

        let new_size = size.next_power_of_two();
        let power_of_two = align > 0 && (align & (align - 1)) == 0;

        align <= HEAP_ALIGNMENT && power_of_two && new_size <= self.heap_size
    }

    /// Allocates a block of memory from the heap.
    fn allocate(&mut self, size: u64, align: u64) -> (pt: u64)
        ensures
            self.wf(),
            self.free_list_valid(),
            pt != 0 ==> self.in_heap_range(pt as nat, size as nat),
            self.params_eq(&old(self)),
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
                self.free_list_valid(),
                order_needed <= order <= len,
                len == self.free_list@.len(),
                self.params_eq(&old(self)),
                self.order_size(order_needed as nat) >= size,
            decreases len - order,
        {
            let ghost prev = *self;

            // Do we have a block of this size? Check head.
            if !self.free_list.index(order).head.is_none() {
                let (first, Tracked(first_points_to)) = self.free_list.update_in_place(
                    order,
                    pop_front_closure,
                // Verus seems not to like the naked closure
                // as the precondition is not inherited into
                // the captured body.
                );

                proof {
                    assert(prev.free_list@.index(order as int).wf());
                    self.lemma_order_size_increases(order_needed as nat, order as nat);
                }

                // If the block is too big, break it up.  This leaves
                // the address unchanged, because we always allocate at
                // the head of a block.
                if order > order_needed {
                    // Split the block into two.
                    self.split_free_block(
                        first,
                        Tracked(first_points_to),
                        order as u64,
                        order_needed as u64,
                    );
                }
                return first.addr() as u64;
            }
            order += 1;
        }

        // If we reach here, we have not found a block of the requested size.
        // Memory exhaustion is very hard to detect in static analysis so we
        // just return 0 to indicate that we cannot allocate anything.
        0
    }

    /// Deallocate a block allocated using `allocate`.
    fn deallocate(&mut self, ptr: u64, size: u64, align: u64)
        ensures
            self.wf(),
            self.free_list_valid(),
            self.params_eq(&old(self)),
    {
        let initial_order = self.allocation_order(size, align);

        // The fun part: When deallocating a block, we also want to check
        // to see if its "buddy" is on the free list.  If the buddy block
        // is also free, we merge them and continue walking up.
        //
        // `block` is the biggest merged block we have so far.
        let mut order = initial_order;
        let len = self.free_list.len() as _;
        let mut ptr = ptr as u64;
        while order < len
            invariant
                len == self.free_list@.len(),
                self.wf(),
                self.free_list_valid(),
                order >= initial_order,
                self.params_eq(&old(self)),
                self.in_heap_range(ptr as nat, size as nat),
                self.order_size(initial_order as nat) >= size,
            decreases len - order,
        {
            let buddy = self.buddy(order, ptr);
            let ghost prev = *self;

            // We have found a valid buddy block to be merged with.
            if buddy != 0 {
                // Check if the buddy block is indeed free.
                if let Some(idx) = self.free_list.index(order as usize).find_by_addr(ptr) {
                    // We have a buddy that is free.
                    let f = |list: LinkedList<()>| -> (res: (
                        (DekoPPtr<Node<()>>, Tracked<DekoHeapBlockPerm>),
                        LinkedList<()>,
                    ))
                        requires
                            list.wf(),
                            self.free_list@.index(order as int) == list,
                        ensures
                            res.0.0 == list.inner@.ptrs.index(idx as int),
                            res.1@ == list@.remove(idx as int),
                            res.1.inner@.ptrs == list.inner@.ptrs.remove(idx as int),
                            res.0.1@.value().value == list@.index(idx as int),
                            res.1.wf(),
                        {
                            assert(0 <= idx < list.inner@.ptrs.len());
                            let mut list = list;
                            let res = list.remove(idx);
                            (res, list)
                        };

                    let (buddy_ptr, Tracked(buddy_points_to)) = self.free_list.update_in_place(
                        order as usize,
                        f,
                    );

                    ptr = ptr.min(buddy_ptr.addr() as u64);
                } else {
                    // If we reach here, we haven't found a buddy block of this size so
                    // we just insert the block into the free list and mark it as free.
                    let (ptr, Tracked(points_to)) = unsafe {
                        // Because we are manipulating the raw memory, we need to
                        // use `from_raw_uninit` to create a pointer from the raw address.
                        // This is safe because we are guaranteed that the address is valid
                        // and the memory is uninitialized by formal verification.
                        //
                        // No allocation is required because we are just casting raw address
                        // into a "node".
                        DekoPPtr::<Node<()>>::from_raw_uninit(ptr)
                    };

                    proof {
                        assume(points_to.is_init());
                        assume(points_to.value().value.wf());
                    }

                    let f = |list: LinkedList<()>| -> (res: ((), LinkedList<()>))
                        requires
                            list.wf(),
                            self.free_list@.index(order as int) == list,
                        ensures
                            res.1.wf(),
                        {
                            let mut list = list;
                            list.push_front_no_alloc(ptr, Tracked(points_to));
                            ((), list)
                        };

                    self.free_list.update_in_place(order as usize, f);
                    return ;
                }
            }
            order += 1;
        }
    }
}

impl<const ORDER: usize> DekoHeap<ORDER> {
    #[verifier::inline]
    pub open spec fn heap_size(&self) -> nat {
        block_size(ORDER as nat)
    }

    pub closed spec fn is_init(&self) -> bool {
        &&& self.heap_base != 0
        &&& self.heap_size != 0
    }

    /// The size of the blocks we allocate for a given order.
    ///
    /// Note that we add the minimum block size to the order to ensure that
    /// the size is at least the minimum block size.
    spec fn order_size(&self, order: nat) -> nat {
        block_size(order + log(2, self.min_block_size as int) as nat)
    }

    /// A helper axiom to unfold the order_size function.
    ///
    /// `compute` does not automatically prove this because of data type
    /// converion confusion but by definition of the `order_size` function
    /// we can easily do this. Proving is also feasible but we don't bother
    /// to do so.
    axiom fn order_size_unfold(&self, order: nat)
        ensures
            self.order_size(order) == pow(2, order + log(2, self.min_block_size as int) as nat),
    ;

    // axiom fn list_extensionality(a: &Self, b: &Self, order: nat, list: &LinkedList<()>)
    //     requires
    //         a.wf(),
    //         a.is_init(),
    //         a.heap_size == b.heap_size,
    //         a.heap_base == b.heap_base,
    //         a.min_block_size == b.min_block_size,
    //         a.free_list@.len() == b.free_list@.len(),
    //         0 <= order < a.free_list@.len(),
    //     ensures
    //         a.blocks_no_overlapping_at(list, a.order_size(order)) && a.blocks_are_aligned(
    //             list,
    //             a.order_size(order),
    //         ) && a.blocks_in_heap_range(list, a.order_size(order)) ==> b.blocks_no_overlapping_at(
    //             list,
    //             a.order_size(order),
    //         ) && b.blocks_are_aligned(list, a.order_size(order)) && b.blocks_in_heap_range(
    //             list,
    //             a.order_size(order),
    //         ),
    // ;
    pub closed spec fn blocks_are_aligned(&self, list: &LinkedList<()>, block_size: nat) -> bool {
        forall|i: int|
            0 <= i < list.inner@.ptrs.len() ==> #[trigger] list.inner@.ptrs.index(i).addr() % (
            block_size as usize) == 0
    }

    pub closed spec fn blocks_in_heap_range(&self, list: &LinkedList<()>, block_size: nat) -> bool {
        forall|i: int|
            0 <= i < list.inner@.ptrs.len() ==> self.in_heap_range(
                #[trigger] list.inner@.ptrs.index(i).addr() as nat,
                block_size,
            )
    }

    /// Ensures that the blocks in the free list at a given order do not overlap.
    pub closed spec fn blocks_no_overlapping_at(
        &self,
        list: &LinkedList<()>,
        block_size: nat,
    ) -> bool {
        // Ensures any two blocks cannot overlap.
        forall|i, j: int|
            0 <= i < list.inner@.ptrs.len() && 0 <= j < list.inner@.ptrs.len() && i != j
                ==> !overlaps_with(
                #[trigger] list.inner@.ptrs.index(i).addr() as nat,
                #[trigger] list.inner@.ptrs.index(j).addr() as nat,
                block_size as nat,
            )
    }

    pub closed spec fn params_eq(&self, other: &Self) -> bool {
        &&& self.heap_base == other.heap_base
        &&& self.heap_size == other.heap_size
        &&& self.min_block_size == other.min_block_size
        &&& self.free_list@.len() == other.free_list@.len()
    }

    /// Ensures that allocating the same memory twice that causes double use problems.
    pub closed spec fn block_no_overlapping(&self) -> bool {
        forall|i: nat|
            0 <= i < self.free_list@.len() ==> {
                let list = #[trigger] self.free_list@.index(i as int);

                &&& self.blocks_no_overlapping_at(&list, self.order_size(i as nat))
                &&& self.blocks_are_aligned(&list, self.order_size(i as nat))
                &&& self.blocks_in_heap_range(&list, self.order_size(i as nat))
            }
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
        &&& u64::MAX > self.heap_size >= self.min_block_size >= core::mem::size_of::<Node<u64>>()
            > 0
        &&& 0 < ORDER <= 32
        &&& u64::MAX >= self.heap_base + self.heap_size
    }

    proof fn lemma_order_size_bounded(&self, order: nat)
        requires
            order < ORDER as nat,
            self.wf(),
        ensures
            self.order_size(order) <= self.heap_size as nat <= (u64::MAX as nat),
    {
        // block_size(order + log(2, self.min_block_size as int) as nat)
        // < block_size(ORDER + log(2, self.min_block_size as int) as nat)
        let n = choose|n: nat|
            self.heap_size == #[trigger] pow(2, n) && self.min_block_size as int == pow(
                2,
                (n - ORDER + 1) as nat,
            ) && n >= ORDER - 1;
        lemma_log_pow(2, (n - ORDER + 1) as nat);
        assert(ORDER + log(2, self.min_block_size as int) as nat == n + 1);
        assert(order + log(2, self.min_block_size as int) as nat <= n);
        lemma_pow_increases(2, order + log(2, self.min_block_size as int) as nat, n);

        // This is safe as we just unfold the definition of order_size.
        // We can add function extensionality to the axiom but it is
        // not so necessary as we can show that the definitions are
        // syntactically the same.
        //
        //The proof is also trivial so we don't bother to write it.
        self.order_size_unfold(order);
    }

    #[verifier::external_body]
    proof fn lemma_order_size_increases(&self, e1: nat, e2: nat)
        requires
            e1 <= e2 <= ORDER as nat,
        ensures
            self.order_size(e1) <= self.order_size(e2),
    {
    }

    /// This lemma ensures that the order plus the minimum block size does not overflow
    /// the maximum value of u32.
    ///
    /// ```
    /// \forall order: \mathbb{N}, order < ORDER ==> order + log(2, min_block_size) < u32::MAX
    /// ```
    ///
    /// This looks trivial to human we need some extra efforts to prove it in verus.
    proof fn lemma_order_plus_min_heap_size(&self, order: nat)
        requires
            self.wf(),
            order < ORDER as nat,
        ensures
            (order + log(2, self.min_block_size as int) as nat) < (u32::MAX as nat),
    {
        let n = choose|n: nat|
            self.heap_size == #[trigger] pow(2, n) && self.min_block_size as int == pow(
                2,
                (n - ORDER + 1) as nat,
            ) && n >= ORDER - 1;
        lemma_log_pow(2, (n - ORDER + 1) as nat);

        lemma2_to64();
        lemma_log_is_ordered(2, self.heap_size as int, u64::MAX as int);
        lemma_log_pow(2, n);

        lemma_log_is_ordered(2, u64::MAX as int, pow2(64) as int);
        lemma_pow2(64);  // this is the reason we don't like pow2 instead of pow(2, n)
        lemma_log_pow(2, 64);
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
            old(self).free_list_valid(),
            valid_heap_param(heap_start, heap_size, ORDER as u64),
        ensures
            self.wf(),
            self.init_ok(),
            self.free_list_valid(),
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
    pub const fn new(Ghost(f): Ghost<DekoHeapPredicate>) -> (s: Self)
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

    fn choose_size(&self, mut size: u64, align: u64) -> (s: u64)
        ensures
            s == vstd::math::max(
                if align > size {
                    align
                } else {
                    size
                } as _,
                self.min_block_size as _,
            ),
    {
        if align > size {
            size = align;
        }
        let size = if size < self.min_block_size {
            self.min_block_size
        } else {
            size
        };

        size
    }

    #[inline(always)]
    fn allocation_size(&self, size: u64, align: u64) -> (s: u64)
        requires
            self.valid_size_and_align(size, align),
        ensures
            s == self.allocation_size_spec(size, align),
            is_power_of_two_spec(s as nat),
            self.min_block_size <= s <= self.heap_size,
            s >= size,
    {
        self.choose_size(size, align).next_power_of_two()
    }

    /// The "order" of an allocation is how many times we need to double
    /// `min_block_size` in order to get a large enough block, as well as
    /// the index we use into `free_lists`.
    #[inline]
    fn allocation_order(&self, old_size: u64, align: u64) -> (r: u64)
        requires
            self.valid_size_and_align(old_size, align),
            self.wf(),
        ensures
            0 <= r < ORDER as u64,
            self.order_size(r as nat) >= old_size,
    {
        let size = self.allocation_size(old_size, align);
        // we now have size >= min_block_size && size >= old_size.
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

            assert(size >= old_size);
            lemma_log_is_ordered(2, old_size as int, size as int);
            self.order_size_unfold(res as nat);
        }

        res as u64 - min_block_size_log2 as u64
    }

    /// Split a block of order `order` down into a block of order `order_needed`, placing
    /// any unused chunks on the free list.
    fn split_free_block(
        &mut self,
        block: DekoHeapBlock,
        Tracked(block_points_to): Tracked<DekoHeapBlockPerm>,
        mut order: u64,
        order_needed: u64,
    )
        requires
            order_needed < order < ORDER,
            old(self).in_heap_range(block.addr() as nat, old(self).order_size(order as nat)),
            old(self).wf(),
            old(self).free_list_valid(),
            old(self).is_init(),
        ensures
            self.wf(),
            self.free_list_valid(),
            self.params_eq(&old(self)),
    {
        let addr = block.addr();  // get the address to the block.
        let min_block_size_log2 = self.min_block_size.ilog2() as u64;
        proof {
            // Ensure no overflow.
            self.lemma_order_plus_min_heap_size(order as nat);
            self.lemma_order_size_bounded(order as nat);
            self.order_size_unfold(order as nat);
        }
        let size = 2u64.pow((order + min_block_size_log2) as u32);
        let mut size_to_split = size;

        while order > order_needed
            invariant
                self.wf(),
                min_block_size_log2 == log(2, self.min_block_size as int),
                ORDER > order > order_needed >= 0,
                size_to_split <= size,
                addr + size <= u64::MAX,
            decreases order - order_needed,
        {
            order -= 1;
            size_to_split /= 2;

            // Insert the upper half of the block into the free list.
            // We will create a "free block" at first.
            let (new_block, Tracked(new_points_to)) = unsafe {
                DekoPPtr::<Node<()>>::from_raw_uninit(addr as u64 + size_to_split)
            };
            proof {
                assume(new_points_to.value().value.wf());
                assume(new_points_to.is_init());
            }

            // Now we insert the block to the free list.
            self.free_list.update_in_place(
                order as usize,
                |list|
                    {
                        let mut list = list;
                        list.push_front_no_alloc(new_block, Tracked(new_points_to));
                        ((), list)
                    },
            );
        }
    }

    proof fn lemma_buddy_offset_in_bounds(&self, size: u64, relative_offset: u64, n: nat)
        requires
    // Assumption 1: heap_size is a power of two.

            0 <= n < 64,
            pow(2, n) == self.heap_size as nat,
            // Assumption 2: The block size is less than the total heap size.
            size < self.heap_size,
            // Assumption 3: The block's offset is within the heap's boundaries.
            relative_offset < self.heap_size,
        ensures
            (relative_offset ^ size) < self.heap_size,
    {
        let heap_size = self.heap_size;
        assert((relative_offset ^ size) == (relative_offset | size) - (relative_offset & size))
            by (bit_vector);
        lemma_lt_is_power_of_two_bitor(heap_size, relative_offset, size, n as u64);
    }

    /// Given a `block` with the specified `order`, find the "buddy" block,
    /// that is, the other half of the block we originally split it from,
    /// and also the block we could potentially merge it with.
    fn buddy(&self, order: u64, ptr: u64) -> (r: u64)
        requires
            self.wf(),
            order < ORDER as u64,
            ptr >= self.heap_base,
        ensures
            ptr + self.order_size(order as nat) >= self.heap_base + self.heap_size ==> r == 0,
    {
        proof {
            self.lemma_order_plus_min_heap_size(order as nat);
            self.lemma_order_size_bounded(order as nat);
            self.order_size_unfold(order as nat);
        }

        let min_block_size_log2 = self.min_block_size.ilog2() as u64;
        let size = 2u64.pow((order + min_block_size_log2) as u32) as u64;

        if ptr >= u64::MAX - size || ptr + size >= self.heap_base + self.heap_size {
            // No buddy at all.
            0
        } else {
            // Fun: We can find our buddy by xoring the right bit in our
            // offset from the base of the heap.
            let relative_offset = ptr - self.heap_base;
            let buddy_offset = relative_offset ^ size;

            proof {
                let n = choose|n: nat| pow(2, n) == self.heap_size;
                lemma2_to64();
                lemma_pow2(64);
                lemma_log_is_ordered(2, u64::MAX as int, pow(2, 64));
                lemma_log_is_ordered(2, self.heap_size as int, u64::MAX as int);
                lemma_log_pow(2, n);
                lemma_log_pow(2, 64);

                self.lemma_buddy_offset_in_bounds(size, relative_offset, n);
            }

            self.heap_base + buddy_offset
        }
    }
}

impl<const ORDER: usize> WellFormed for DekoHeap<ORDER> {
    closed spec fn wf(&self) -> bool {
        &&& self.is_init()
        &&& self.heap_size_valid()
        &&& self.free_list@.len() == ORDER as int
        &&& ORDER - 1 >= 0
    }
}

} // verus!
