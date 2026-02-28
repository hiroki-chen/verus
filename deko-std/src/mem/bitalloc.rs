//! A bitmap-based bit allocator implementation.
//!
//! This codebase still have a large amount of unverified code; we plan to
//! incrementally verify more parts of it in the future.
use core::ops::Index;

use deko_macros::DekoDebug;
use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power::pow;
use vstd::invariant;
use vstd::prelude::*;

use crate::{is_power_of_two_spec, Array, WellFormed};

verus! {

pub proof fn lemma_bit_map_allocator_1024_is_pow2()
    ensures
        is_power_of_two_spec(<DekoBitmapAllocator1024 as DekoBitAlloc>::cap_spec() as nat),
{
    admit();
}

pub open spec fn sum_over_arr<T: DekoBitAlloc + WellFormed>(arr: Seq<T>, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        arr[(n - 1) as int].used_spec() as usize + sum_over_arr(arr, (n - 1) as nat) as usize
    }
}

pub type DekoBitmapAllocator1024 = DekoBitmapAllocatorTree<BitmapAllocator64>;

pub assume_specification[ u64::count_ones ](b: u64) -> (r: u32)
    ensures
        r as int == count_ones_spec(b),
;

#[verifier::opaque]
pub open spec fn count_ones_spec(b: u64) -> int
    decreases b,
{
    if b == 0 {
        0
    } else {
        proof {
            assert(b & ((b - 1) as u64) < b) by (bit_vector)
                requires
                    b > 0,
            ;
        }

        1 + count_ones_spec(b & (b - 1) as u64)
    }
}

/// A proof that count_ones_spec returns a value within bounds, i.e.,
/// counting bits never yields a negative number or a number larger than 64.
#[verifier::spinoff_prover]
pub proof fn lemma_count_ones_spec_bounds(b: u64)
    ensures
        0 <= count_ones_spec(b) <= u64::BITS as int,
    decreases b,
{
    if b == 0 {
        reveal(count_ones_spec);
    } else {
        admit();
    }
}

pub broadcast axiom fn alloc_bits_size_wf<T: DekoBitAlloc + WellFormed>()
    ensures
        #[trigger] Array::<T, 16>::size_wf(),
;

#[derive(Clone, Copy, DekoDebug)]
pub struct BitmapAllocator64 {
    #[deko(hex)]
    pub bits: u64,
}

impl WellFormed for BitmapAllocator64 {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl View for BitmapAllocator64 {
    type V = u64;

    open spec fn view(&self) -> Self::V {
        self.bits
    }
}

impl BitmapAllocator64 {
    pub const fn new_full() -> (r: Self)
        ensures
            r@ == u64::MAX,
    {
        BitmapAllocator64 { bits: u64::MAX }
    }

    pub const fn new_empty() -> (r: Self)
        ensures
            r@ == 0,
    {
        BitmapAllocator64 { bits: 0 }
    }
}

/// A trait for types that can be used as bit allocators.
///
/// common ensures should be in the trait definition.
pub trait DekoBitAlloc: Sized + WellFormed {
    open spec fn type_inv() -> bool {
        true
    }

    spec fn cap_spec() -> int;

    spec fn used_spec(&self) -> int;

    /// Count how many bits are set (allocated) in a range
    #[verifier::inline]
    open spec fn count_set_in_range(&self, start: int, len: int) -> int {
        // Sum of 1s in the range
        Seq::new(
            len as nat,
            |i: int|
                if self.is_allocated(start + i) {
                    1int
                } else {
                    0int
                },
        ).fold_left(0int, |acc: int, x: int| acc + x)
    }

    /// Checks if the bit at the given offset is allocated.
    spec fn is_allocated(&self, offset: int) -> bool;

    /// Checks if the range [start, start + len) is free (not allocated).
    #[verifier::inline]
    open spec fn is_range_free(&self, start: int, len: int) -> bool {
        forall|i: int| start <= i < start + len ==> !self.is_allocated(i)
    }

    /// The capacity() of the allocator in number of bits.
    /// This function replaces the associated constant as
    /// Verus doesn't support it.
    fn cap() -> (r: usize)
        requires
            0 <= Self::cap_spec() < usize::MAX as int,
            Self::type_inv(),
        ensures
            r == Self::cap_spec() as usize,
            r > 0,
        opens_invariants none
        no_unwind
    ;

    /// The common implementation for aligned allocation.
    ///
    /// This function is very _complicated_ to verify so the reader
    /// should be extra careful when modifying it.
    #[verifier::external_body]
    // #[verifier::spinoff_prover]
    fn alloc_aligned(&mut self, entries: usize, align: usize) -> (r: Option<usize>)
        requires
            0 <= Self::cap_spec() < usize::MAX as int,
            (entries as int) <= Self::cap_spec(),
            is_power_of_two_spec(Self::cap_spec() as nat),
            Self::type_inv(),
            old(self).wf(),
            (align as int) < log(2, Self::cap_spec()),
        ensures
            self.wf(),
            match r {
                Some(start) => {
                    &&& start % align == 0
                    &&& start + entries <= Self::cap_spec()
                    &&& self.used_spec() == old(self).used_spec() + entries as int
                    &&& forall|i: int|
                        start as int <= i < (start + entries) as int ==> self.is_allocated(i)
                    &&& old(self).is_range_free(start as int, entries as int)
                    &&& forall|i: int|
                        0 <= i < Self::cap_spec() && !(start <= i < start + entries)
                            ==> self.is_allocated(i) == old(self).is_allocated(i)
                },
                None => *self == *old(self),  // nothing has ever changed.
            },
    {
        if entries == 0 {
            // This is a no-op allocation.
            return None;
        }
        // This proves that the step itself will not overflow/underflow.

        proof {
            assert(log(2, Self::cap_spec()) <= usize::BITS) by {
                broadcast use vstd::arithmetic::power::group_pow_properties;

                vstd::arithmetic::power2::lemma2_to64();
                vstd::arithmetic::power2::lemma_pow2(64);

                vstd::arithmetic::logarithm::lemma_log_is_ordered(2, usize::MAX as int, pow(2, 64));
                vstd::arithmetic::logarithm::lemma_log_is_ordered(
                    2,
                    Self::cap_spec(),
                    usize::MAX as int,
                );

                vstd::arithmetic::logarithm::lemma_log_pow(2, 64);
            }

            assert(align < log(2, Self::cap_spec()) <= usize::BITS);
            assert(0 < 1u64 << align <= usize::MAX as int) by (bit_vector)
                requires
                    align < usize::BITS,
            ;

            assert(Self::cap_spec() - (entries as int) >= 0);
        }

        let align_mask = (1usize << align) - 1;
        let align_step = 1usize << align;

        let len = Self::cap() - entries;
        let mut offset = 0;

        // Fix the loop invariant.
        while offset <= len
            invariant
                Self::type_inv(),
                self.wf(),
                align_step == 1usize << align,
                align_mask == (1usize << align) - 1,
            decreases len - offset,
        {
            if let Some(offset_free) = self.next_free(offset) {
                // If the next free offset doesn't satisfy the alignment, skip ahead.
                if offset_free != offset {
                    proof {
                        // TODO: Prove that offset is bounded via below operation.
                    }

                    offset = ((offset_free - 1) & !align_mask) + (1 << align);
                    continue ;
                }
                // The aligned offset is free. Keep checking the next bit until we
                // reach the requested size.

                let mut free_entries = 0;
                for size_check in offset..(offset + entries) {
                    if !self.get(size_check) {
                        free_entries += 1;
                    } else {
                        break ;
                    }
                }

                if free_entries == entries {
                    self.set(offset, entries, true);
                    return Some(offset);
                }
            }
            offset += align_step;
        }

        None
    }

    fn alloc(&mut self, entries: usize, align: usize) -> (r: Option<usize>)
        requires
            0 <= Self::cap_spec() < usize::MAX as int,
            Self::type_inv(),
            (entries as int) <= Self::cap_spec(),
            old(self).wf(),
            is_power_of_two_spec(Self::cap_spec() as nat),
            (align as int) < log(2, Self::cap_spec()),
        ensures
            self.wf(),
    ;

    fn free(&mut self, start: usize, entries: usize)
        requires
            0 <= Self::cap_spec() < usize::MAX as int,
            old(self).wf(),
            entries > 0,
            start + entries <= Self::cap_spec() as usize,
        ensures
            self.wf(),
        opens_invariants none
        no_unwind
    ;

    fn set(&mut self, start: usize, entries: usize, value: bool)
        requires
            old(self).wf(),
            0 <= Self::cap_spec() < usize::MAX as int,
            entries > 0,
            start + entries <= Self::cap_spec() as usize,
        opens_invariants none
        no_unwind
    ;

    fn next_free(&self, start: usize) -> Option<usize>
        requires
            Self::type_inv(),
            0 <= Self::cap_spec() < usize::MAX as int,
            self.wf(),
            start < Self::cap_spec() as usize,
    ;

    fn get(&self, offset: usize) -> (r: bool)
        requires
            Self::type_inv(),
            self.wf(),
            0 <= Self::cap_spec() < usize::MAX as int,
            offset < Self::cap_spec() as usize,
        ensures
            r == self.is_allocated(offset as int),
    ;

    fn empty(&self) -> bool
        requires
            self.wf(),
            0 <= Self::cap_spec() < usize::MAX as int,
    ;

    fn capacity(&self) -> (r: usize)
        requires
            self.wf(),
            0 <= Self::cap_spec() < usize::MAX as int,
            Self::type_inv(),
        ensures
            r > 0,  // r === 0 panics log
    ;

    fn used(&self) -> usize
        requires
            self.wf(),
            0 <= Self::cap_spec() < usize::MAX as int,
        returns
            self.used_spec() as usize,
    ;
}

impl DekoBitAlloc for BitmapAllocator64 {
    #[verifier::inline]
    open spec fn cap_spec() -> int {
        u64::BITS as int
    }

    #[verifier::inline]
    open spec fn is_allocated(&self, offset: int) -> bool {
        self.bits & (1u64 << offset) != 0
    }

    #[verifier::inline]
    open spec fn used_spec(&self) -> int {
        count_ones_spec(self.bits)
    }

    fn cap() -> usize {
        u64::BITS as _
    }

    #[inline]
    fn alloc(&mut self, entries: usize, align: usize) -> (r: Option<usize>)
        ensures
            self.wf(),
    {
        Self::alloc_aligned(self, entries, align)
    }

    #[inline]
    fn free(&mut self, start: usize, entries: usize)
        ensures
            self.wf(),
            // Freed entries are now marked as not allocated
            forall|i: int| #![auto] start <= i < start + entries ==> !self.is_allocated(i),
            // Other entries remain unchanged
            forall|i: int|
                #![auto]
                0 <= i < 64 && !(start <= i < start + entries) ==> self.is_allocated(i) == old(
                    self,
                ).is_allocated(i),
    {
        self.set(start, entries, false);
    }

    fn set(&mut self, start: usize, entries: usize, value: bool)
        ensures
            self.wf(),
            forall|i: int| #![auto] start <= i < start + entries ==> self.is_allocated(i) == value,
            // Other entries remain unchanged
            forall|i: int|
                #![auto]
                0 <= i < 64 && !(start <= i < start + entries) ==> self.is_allocated(i) == old(
                    self,
                ).is_allocated(i),
    {
        proof {
            assert(0 < 1u64 << start <= u64::MAX) by (bit_vector)
                requires
                    entries > 0,
                    start + entries <= 64,
            ;

            assert(start + entries - 1 >= 0);
            let p = (start + entries - 1) as u64;

            assert(1u64 << p > 0) by (bit_vector)
                requires
                    p >= 0,
                    p < u64::BITS,
            ;

            assert(((((1u64 << p) - 1) as u64) << 1) + 1 <= u64::MAX) by (bit_vector)
                requires
                    p >= 0,
                    p < u64::BITS,
            ;
        }

        // Create a mask for changing the bitmap
        let start_mask = !((1u64 << start) - 1);
        // Need to do some bit shifting to avoid overflow when top bit set
        let end_mask = (((1 << (start + entries - 1)) - 1) << 1) + 1;
        let mask = start_mask & end_mask;

        proof {
            assert forall|i: u64| #![auto] 0 <= i < 64 implies ((mask >> i) & 1 == 1) <==> (start
                <= i < start + entries) by {
                if start + entries < 64 {
                    assert(((mask >> i) & 1 == 1) <==> (start <= i < start + entries))
                        by (bit_vector)
                        requires
                            mask == start_mask & end_mask,
                            start_mask == !(((1u64 << start) as u64 - 1) as u64),
                            end_mask == ((((1u64 << (start + entries - 1) as u64) - 1) as u64)
                                << 1u64) + 1,
                            start + entries - 1 >= 0,
                            start + entries < 64,
                            0 <= i < 64,
                    ;
                }
                if start + entries == 64 {
                    assert(end_mask == u64::MAX) by (bit_vector)
                        requires
                            end_mask == ((((1u64 << (start + entries - 1) as u64) - 1) as u64)
                                << 1u64) + 1,
                            start + entries == 64,
                    ;

                    assert(((mask >> i) & 1 == 1) <==> (start <= i < start + entries))
                        by (bit_vector)
                        requires
                            mask == start_mask & end_mask,
                            start_mask == !(((1u64 << start) as u64 - 1) as u64),
                            end_mask == u64::MAX,
                            start + entries == 64,
                            0 <= i < 64,
                    ;
                }
            }
        }

        let ghost old_bits = self.bits;

        if value {
            self.bits = self.bits | mask;

            proof {
                let self_bits = self.bits;

                assert forall|i: u64|
                    #![auto]
                    start <= i < start + entries implies self.is_allocated(i as int) by {
                    assert(0 <= i < 64);  // for the trigger.
                    assert(((mask >> i) & 1) == 1);
                    assert((self_bits & (1u64 << i)) != 0) by (bit_vector)
                        requires
                            self_bits == (old_bits | mask),
                            ((mask >> i) & 1) == 1,
                            0 <= i < 64,
                    ;
                }

                assert forall|i: u64|
                    #![auto]
                    0 <= i < 64 && !(start <= i < start + entries) implies self.is_allocated(
                    i as int,
                ) == old(self).is_allocated(i as int) by {
                    let self_bits = self.bits;

                    // Explicitly instantiate the proven biconditional for this i
                    // It was proven for u64, so cast i
                    assert(((mask >> (i as u64)) & 1 == 1) <==> (start <= i < start + entries));

                    // We know !(start <= i < start + entries)
                    // By contrapositive: ((mask >> (i as u64)) & 1) != 1

                    // Since (x & 1) is either 0 or 1:
                    assert(((mask >> (i as u64)) & 1) == 0 || ((mask >> (i as u64)) & 1) == 1)
                        by (bit_vector);

                    // Therefore it must be 0
                    assert(((mask >> (i as u64)) & 1) == 0);

                    assert((self_bits & (1u64 << (i as u64))) == (old_bits & (1u64 << (i as u64))))
                        by (bit_vector)
                        requires
                            self_bits == (old_bits | mask),
                            ((mask >> (i as u64)) & 1) == 0,
                            0 <= (i as u64) < 64,
                    ;
                };
            }
        } else {
            self.bits = self.bits & !mask;

            proof {
                let self_bits = self.bits;

                // Bits in range are cleared
                assert forall|i: u64|
                    #![auto]
                    start <= i < start + entries implies !self.is_allocated(i as int) by {
                    assert(0 <= i < 64);  // for the trigger.
                    assert(((mask >> i) & 1) == 1);
                    assert((self_bits & (1u64 << i)) == 0) by (bit_vector)
                        requires
                            self_bits == (old_bits & !mask),
                            ((mask >> i) & 1) == 1,
                            0 <= i < 64,
                    ;
                };

                assert forall|i: u64|
                    #![auto]
                    0 <= i < 64 && !(start <= i < start + entries) implies self.is_allocated(
                    i as int,
                ) == old(self).is_allocated(i as int) by {
                    let self_bits = self.bits;

                    // Explicitly instantiate the proven biconditional for this i
                    // It was proven for u64, so cast i
                    assert(((mask >> (i as u64)) & 1 == 1) <==> (start <= i < start + entries));

                    // We know !(start <= i < start + entries)
                    // By contrapositive: ((mask >> (i as u64)) & 1) != 1

                    // Since (x & 1) is either 0 or 1:
                    assert(((mask >> (i as u64)) & 1) == 0 || ((mask >> (i as u64)) & 1) == 1)
                        by (bit_vector);

                    // Therefore it must be 0
                    assert(((mask >> (i as u64)) & 1) == 0);

                    assert((self_bits & (1u64 << (i as u64))) == (old_bits & (1u64 << (i as u64))))
                        by (bit_vector)
                        requires
                            self_bits == (old_bits & !mask),  // adjust for | mask in the other branch
                            ((mask >> (i as u64)) & 1) == 0,
                            0 <= (i as u64) < 64,
                    ;
                };
            }
        }
    }

    fn next_free(&self, start: usize) -> Option<usize> {
        proof {
            assert(0 < 1u64 << start <= u64::MAX) by (bit_vector)
                requires
                    start < 64,
            ;
        }

        let mask = (1 << start) - 1;
        let idx = (self.bits | mask).trailing_ones() as usize;
        if idx < Self::cap() {
            Some(idx)
        } else {
            None
        }
    }

    #[inline]
    fn get(&self, offset: usize) -> (r: bool)
        ensures
            r == self.is_allocated(offset as int),
    {
        self.bits & (1 << offset) != 0
    }

    #[inline]
    fn empty(&self) -> bool {
        self.bits != 0
    }

    #[inline]
    fn capacity(&self) -> usize {
        Self::cap()
    }

    #[inline]
    fn used(&self) -> (r: usize)
        ensures
            r <= 64,
    {
        proof {
            lemma_count_ones_spec_bounds(self.bits);
        }

        self.bits.count_ones() as usize
    }
}

/// A bitmap-based allocator tree structure with cascading allocation.
///
/// Thus an allocator can have child allocators, and when an allocation
/// request cannot be satisfied by the current allocator, it can delegate
/// the request to its child allocators.
#[derive(DekoDebug)]
#[verifier::reject_recursive_types(T)]
pub struct DekoBitmapAllocatorTree<T: DekoBitAlloc + deko_std::fmt::DekoDebug> {
    #[deko(hex)]
    pub bitset: u16,
    #[deko(hex)]
    pub child: Array<T, 16>,
}

impl<T: DekoBitAlloc + deko_std::fmt::DekoDebug> WellFormed for DekoBitmapAllocatorTree<T> {
    open spec fn wf(&self) -> bool {
        &&& self.child.wf()
        &&& forall|i: int| 0 <= i && i < 16 ==> #[trigger] self.child@[i].wf()
        &&& T::cap_spec()
            <= usize::MAX as int
        // The i-th bit of bitset is set iff the i-th child is not empty.
        &&& forall|i: int|
            #![trigger self.child@[i].used_spec()]
            0 <= i < 16 ==> {
                let child_is_not_empty = self.child@[i].used_spec() > 0;
                let bit_is_set = (self.bitset & (1u16 << i)) != 0;
                child_is_not_empty <==> bit_is_set
            }
    }
}

impl DekoBitmapAllocatorTree<BitmapAllocator64> {
    /// Proof task: prove that child_is_set <==> bit_is_set
    #[verifier::external_body]
    pub const fn new_full() -> (r: Self)
        ensures
            r.wf(),
    {
        broadcast use alloc_bits_size_wf;

        Self { bitset: u16::MAX, child: Array::fill(BitmapAllocator64::new_full()) }
    }

    /// Proof task: prove that child_is_set <==> bit_is_set
    #[verifier::external_body]
    pub const fn new_empty() -> (r: Self)
        ensures
            r.wf(),
    {
        broadcast use alloc_bits_size_wf;

        Self { bitset: 0, child: Array::fill(BitmapAllocator64::new_empty()) }
    }
}

impl<T: DekoBitAlloc + deko_std::fmt::DekoDebug> DekoBitAlloc for DekoBitmapAllocatorTree<T> {
    open spec fn cap_spec() -> int {
        (16 * T::cap_spec())
    }

    open spec fn is_allocated(&self, offset: int) -> bool {
        self.child@[offset / T::cap_spec()].is_allocated(offset % T::cap_spec())
    }

    open spec fn used_spec(&self) -> int {
        sum_over_arr(self.child@, 16)
    }

    fn cap() -> (r: usize)
        ensures
            r > 0,
    {
        proof {
            assert(Self::cap_spec() <= usize::MAX as int);
            assert(((16 * T::cap_spec())) <= usize::MAX);
        }

        16 * T::cap()
    }

    open spec fn type_inv() -> bool {
        &&& T::type_inv()
        &&& 0 < T::cap_spec() <= usize::MAX as int
    }

    #[inline]
    fn alloc(&mut self, entries: usize, align: usize) -> (r: Option<usize>)
        ensures
            self.wf(),
            match r {
                Some(start) => {
                    &&& start % align == 0
                    &&& start + entries <= Self::cap_spec()
                    &&& self.used_spec() == old(self).used_spec() + entries as int
                    &&& forall|i: int|
                        start as int <= i < (start + entries) as int ==> self.is_allocated(i)
                    &&& old(self).is_range_free(start as int, entries as int)
                    &&& forall|i: int|
                        0 <= i < Self::cap_spec() && !(start <= i < start + entries)
                            ==> self.is_allocated(i) == old(self).is_allocated(i)
                },
                None => *self == *old(self),  // nothing has ever changed.
            },
    {
        Self::alloc_aligned(self, entries, align)
    }

    #[inline]
    fn free(&mut self, start: usize, entries: usize)
        ensures
            self.wf(),
    {
        self.set(start, entries, false);
    }

    #[verifier::external_body]
    fn set(&mut self, start: usize, entries: usize, value: bool)
        ensures
            self.wf(),
    {
        let mut offset = start % T::cap();
        let mut remain = entries;
        for index in (start / T::cap())..16 {
            let child_size = if remain > (T::cap() - offset) {
                T::cap() - offset
            } else {
                remain
            };
            remain -= child_size;

            // Update in place.
            self.child.0[index].set(offset, child_size, value);
            if self.child.index(index).empty() {
                self.bitset &= !(1 << index);
            } else {
                self.bitset |= 1 << index;
            }
            if remain == 0 {
                break ;
            }
            // Only the first loop iteration uses a non-zero offset

            offset = 0;
        }
    }

    #[verifier::external_body]
    fn next_free(&self, start: usize) -> Option<usize> {
        // vstd::vpanic!()
        let mut offset = start % T::cap();
        for index in (start / T::cap())..16 {
            if let Some(next_offset) = self.child.index(index).next_free(offset) {
                return Some(next_offset + (index * T::cap()));
            }
            // Only the first loop iteration uses a non-zero offset

            offset = 0;
        }
        None
    }

    fn get(&self, offset: usize) -> (r: bool)
        ensures
            r == self.is_allocated(offset as int),
    {
        let index = offset / T::cap();

        proof {
            assert((offset as int) < Self::cap_spec());
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(16, T::cap_spec());
            vstd::arithmetic::div_mod::lemma_div_by_multiple_is_strongly_ordered(
                offset as int,
                Self::cap_spec(),
                16,
                T::cap_spec(),
            );
        }

        self.child.index(offset / T::cap()).get(offset % T::cap())
    }

    fn empty(&self) -> bool {
        self.bitset == 0
    }

    fn capacity(&self) -> usize {
        Self::cap()
    }

    fn used(&self) -> usize {
        let mut sum = 0usize;
        let mut i = 0;
        while i < self.child.len()
            invariant
                i <= self.child@.len(),
                self.wf(),
                self.child.wf(),
                0 <= <BitmapAllocator64 as DekoBitAlloc>::cap_spec() < usize::MAX as int,
                0 <= <Self as DekoBitAlloc>::cap_spec() < usize::MAX as int,
                sum == sum_over_arr(self.child@, i as nat) as usize,
            decreases self.child@.len() - i,
        {
            let Some(new_sum) = sum.checked_add(self.child.index(i).used()) else {
                vstd::vpanic!("Overflow in used()");
            };

            i += 1;

            proof {
                reveal(sum_over_arr);
                assert(i > 0);
                assert(new_sum == (self.child@[i - 1].used_spec() as usize + sum_over_arr(
                    self.child@,
                    (i - 1) as nat,
                ) as usize) as usize);
                assert(new_sum == sum_over_arr(self.child@, i as nat) as usize);
            }

            sum = new_sum;
        }

        sum
    }
}

} // verus!
