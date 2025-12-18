//! A bitmap-based bit allocator implementation.
use deko_macros::DekoDebug;
use vstd::prelude::*;

use crate::{is_power_of_two_spec, Array, WellFormed};

verus! {

pub type DekoBitmapAllocator1024 = DekoBitmapAllocatorTree<BitmapAllocator64>;

pub assume_specification[ u64::count_ones ](b: u64) -> (r: u32)
    ensures
        r as int == count_ones_spec(b),
;

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

pub broadcast axiom fn alloc_bits_size_wf<T: DekoBitAlloc + WellFormed>()
    ensures
        #[trigger] Array::<T, 16>::size_wf(),
;

#[derive(Clone, Copy, DekoDebug)]
pub struct BitmapAllocator64 {
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
pub trait DekoBitAlloc: Sized + WellFormed {
    open spec fn size_wf() -> bool {
        // no overflowing!
        Self::cap_spec() < usize::MAX
    }

    open spec fn type_inv() -> bool {
        true
    }

    spec fn cap_spec() -> int;

    spec fn used_spec(&self) -> int;

    /// The capacity of the allocator in number of bits.
    /// This function replaces the associated constant as
    /// Verus doesn't support it.
    fn cap() -> (r: usize)
        requires
            Self::size_wf(),
            Self::type_inv(),
        ensures
            r == Self::cap_spec(),
    ;

    fn alloc(&mut self, entries: usize, align: usize) -> (r: Option<usize>)
        requires
            Self::size_wf(),
            old(self).wf(),
            is_power_of_two_spec(align as nat),
            align <= Self::cap_spec() as usize,
        ensures
            self.wf(),
    ;

    fn free(&mut self, start: usize, entries: usize)
        requires
            Self::size_wf(),
            old(self).wf(),
            entries > 0,
            start + entries <= Self::cap_spec() as usize,
        ensures
            self.wf(),
    ;

    fn set(&mut self, start: usize, entries: usize, value: bool)
        requires
            old(self).wf(),
            Self::size_wf(),
            entries > 0,
            start + entries <= Self::cap_spec() as usize,
    ;

    fn next_free(&self, start: usize) -> Option<usize>
        requires
            Self::size_wf(),
            self.wf(),
            start < Self::cap_spec() as usize,
    ;

    fn get(&self, offset: usize) -> bool
        requires
            Self::size_wf(),
            self.wf(),
            offset < Self::cap_spec() as usize,
    ;

    fn empty(&self) -> bool
        requires
            self.wf(),
            Self::size_wf(),
    ;

    fn capacity(&self) -> usize
        requires
            self.wf(),
            Self::size_wf(),
            Self::type_inv(),
    ;

    fn used(&self) -> usize
        requires
            self.wf(),
            Self::size_wf(),
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
        // vstd::vpanic!()
        None
    }

    #[inline]
    fn free(&mut self, start: usize, entries: usize)
        ensures
            self.wf(),
    {
        self.set(start, entries, false);
    }

    fn set(&mut self, start: usize, entries: usize, value: bool)
        ensures
            self.wf(),
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

        if value {
            self.bits = self.bits | mask;
        } else {
            self.bits = self.bits & !mask;
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
    fn get(&self, offset: usize) -> bool {
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
    fn used(&self) -> usize {
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
    pub bitset: u16,
    pub child: Array<T, 16>,
}

impl<T: DekoBitAlloc + deko_std::fmt::DekoDebug> WellFormed for DekoBitmapAllocatorTree<T> {
    open spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i && i < 16 ==> #[trigger] self.child@[i].wf()
        &&& T::size_wf()
    }
}

impl DekoBitmapAllocatorTree<BitmapAllocator64> {
    pub const fn new_full() -> (r: Self) {
        broadcast use alloc_bits_size_wf;

        Self { bitset: u16::MAX, child: Array::fill(BitmapAllocator64::new_full()) }
    }

    pub const fn new_empty() -> (r: Self) {
        broadcast use alloc_bits_size_wf;

        Self { bitset: 0, child: Array::fill(BitmapAllocator64::new_empty()) }
    }
}

impl<T: DekoBitAlloc + deko_std::fmt::DekoDebug> DekoBitAlloc for DekoBitmapAllocatorTree<T> {
    open spec fn cap_spec() -> int {
        (16 * T::cap_spec())
    }

    open spec fn used_spec(&self) -> int {
        let s = Seq::new(16, |i: int| self.child@[i].used_spec());
        s.fold_left(0, |acc: int, x: int| acc + x)
    }

    fn cap() -> usize {
        proof {
            assert(Self::size_wf());
            assert(((16 * T::cap_spec())) < usize::MAX);
        }

        16 * T::cap()
    }

    open spec fn type_inv() -> bool {
        &&& T::type_inv()
        &&& T::size_wf()
    }

    fn alloc(&mut self, entries: usize, align: usize) -> (r: Option<usize>)
        ensures
            self.wf(),
            r matches Some(r) ==> {
                &&& r % align == 0
                &&& r + entries <= Self::cap_spec()
            },
    {
        vstd::vpanic!("todo")
    }

    fn free(&mut self, start: usize, entries: usize)
        ensures
            self.wf(),
    {
    }

    fn set(&mut self, start: usize, entries: usize, value: bool)
        ensures
            self.wf(),
    {
        // vstd::vpanic!()
    }

    fn next_free(&self, start: usize) -> Option<usize> {
        // vstd::vpanic!()
        None
    }

    fn get(&self, offset: usize) -> bool {
        true
    }

    fn empty(&self) -> bool {
        self.bitset == 0
    }

    fn capacity(&self) -> usize {
        Self::cap()
    }

    fn used(&self) -> usize {
        vstd::vpanic!("todo")
    }
}

} // verus!
