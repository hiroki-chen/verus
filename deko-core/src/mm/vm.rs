use core::cmp::Ordering;
use core::ops::{Range, RangeBounds};

use deko_macros::DekoDebug;
use deko_std::prelude::*;
use vstd::prelude::*;
use vstd::std_specs::cmp::*;

use super::frame_allocator::DekoAllocatorApi;
use crate::collections::{
    binary_search_by_spec, comparator_consistent_spec, is_sorted_spec, lemma_cmp_pivot_monotonic,
    Vec,
};
use crate::mm::paging::{PageTable, PageTablePermission, PteFlags, Pte_ALL_BITS};
use crate::{kunimplemented, vec};

verus! {

/// Granularity of ranges mapped by [`VirtualMemoryRegion`]. The mapped region of a
/// [`VirtualMemoryRegion`] is always a multiple of this constant.
/// One [`VMR_GRANULE`] covers one top-level page-table entry on x86-64 with
/// 4-level paging.
pub const VMR_GRANULE: u64 = PAGE_SIZE * 512 * 512 * 512;

pub const VMR_NAME_MAX_LEN: usize = 32;

/// This struct manages the mappings in a region of the virtual address space.
///
/// This struct should be either protected by a lock or requires exclusive permission
/// to write to it.
#[derive(DekoDebug)]
pub struct VirtualMemoryRegion {
    /// Start address of this range as virtual PFN (VirtAddr >> PAGE_SHIFT).
    pub start_pfn: u64,
    /// End address of this range as virtual PFN (VirtAddr >> PAGE_SHIFT)
    pub end_pfn: u64,
    /// Global to all mappings in this virtual memory region.
    #[deko(skip)]
    pub pt_flags: PteFlags,
    /// All the virtual memory areas managed by this region.
    ///
    /// FIXME: This data structure is not efficient for lookups. We may need to change it to
    /// an interval tree or other more efficient data structures but not verification-friendly.
    #[deko(skip)]
    pub areas: Vec<VirtualMemory>,
    /// The top-level page tables for this region.
    pub pgtable: DekoPPtr<PageTable>,
}

/// Tracks the corresponding permissions for a virtual memory region if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryRegionPermission {
    /// A collection of page table permissions for each top-level page table.
    pub pgtable_perm: PageTablePermission,
    /// A list of virtual memory permissions managed by this region.
    pub vm_perms: Ghost<Seq<VirtualMemoryPermission>>,
}

/// This struct manages one piece of virtual memory covered by the [`VirtualMemoryRegion`].
#[derive(DekoDebug)]
pub struct VirtualMemory {
    /// The range of virtual addresses covered by this region.
    pub range: Range<VirtAddr>,
    /// The page table entry flags for this region.
    #[deko(skip)]
    pub flags: PteFlags,
    // The pointer to the underlying memory.
    // pub ptr: RwLockNoPred<ReprPtr<M>>, ??? possibly with some generics.
    // but this requires some transformation techniques.
}

/// Tracks the corresponding permissions for a virtual memory if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryPermission {}

impl WellFormed for VirtualMemoryRegion {
    open spec fn wf(&self) -> bool {
        &&& self.start_pfn < self.end_pfn <= u64::MAX / PAGE_SIZE
        &&& self.start_pfn % VMR_GRANULE == 0
        &&& self.end_pfn % VMR_GRANULE == 0
        &&& self.pt_flags.wf()
        &&& self.pt_flags.bits() & Pte_ALL_BITS == self.pt_flags.bits()
        &&& self.pgtable_consistent()
        &&& forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int
                ==> self.areas@[i].wf()
        // Ensure no overlapping areas.
        &&& forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() - 1 as int ==> {
                &&& self.areas@[i].range.end@ <= self.areas@[i + 1].range.start@
            }
        &&& is_sorted_spec(self.areas@)
    }
}

impl WellFormed for VirtualMemory {
    open spec fn wf(&self) -> bool {
        &&& self.range.wf()
        &&& self.range.start@ % PAGE_SIZE == 0
        &&& self.range.end@ % PAGE_SIZE == 0
        &&& self.flags.bits() & Pte_ALL_BITS == self.flags.bits()
        &&& self.flags.wf()
    }
}

impl PartialEq for VirtualMemory {
    #[verifier::external_body]
    fn eq(&self, other: &Self) -> bool {
        self.range.start.0 == other.range.start.0 && self.range.end.0 == other.range.end.0
    }
}

impl PartialOrd for VirtualMemory {
    // Verus has some problem dealing with this.
    #[verifier::external_body]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        if self.range.start.0 < other.range.start.0 {
            Some(core::cmp::Ordering::Less)
        } else if self.range.start.0 > other.range.start.0 {
            Some(core::cmp::Ordering::Greater)
        } else {
            Some(core::cmp::Ordering::Equal)
        }
    }
}

impl PartialEqSpecImpl for VirtualMemory {
    closed spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        &&& self.range.start.0 == other.range.start.0
        &&& self.range.end.0 == other.range.end.0
    }
}

impl PartialOrdSpecImpl for VirtualMemory {
    closed spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<core::cmp::Ordering> {
        if self.range.start@ < other.range.start@ {
            Some(core::cmp::Ordering::Less)
        } else if self.range.start@ > other.range.start@ {
            Some(core::cmp::Ordering::Greater)
        } else {
            Some(core::cmp::Ordering::Equal)
        }
    }
}

#[verus_verify]
impl VirtualMemoryRegion {
    pub open spec fn wf_with(&self, perm: &VirtualMemoryRegionPermission) -> bool {
        &&& perm.pgtable_perm.wf()
        &&& perm.pgtable_perm.pgtable_perm.pptr() == self.pgtable@
        &&& perm.vm_perms@.len() == self.areas@.len()
    }

    pub open spec fn pgtable_consistent(&self) -> bool {
        true
    }

    pub open spec fn compatible_spec(&self, vm_block: &VirtualMemory) -> bool {
        &&& vm_block.range.start@ >= self.start_pfn * PAGE_SIZE
        &&& vm_block.range.end@ <= self.end_pfn * PAGE_SIZE
    }

    pub open spec fn nonoverlapping_block(&self, vm_block: &VirtualMemory) -> bool {
        forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int ==> { !self.areas@[i].overlap_with_spec(vm_block) }
    }

    /// Checks if a given `vm_block` is compatible within this virtual memory region.
    ///
    /// This method returns true if the `vm_block` is within the range of this region.
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            vm_block.wf(),
        returns
            self.compatible_spec(vm_block),
    )]
    pub fn compatible(&self, vm_block: &VirtualMemory) -> bool {
        vm_block.range.start.0 >= self.start_pfn * PAGE_SIZE && vm_block.range.end.0 <= self.end_pfn
            * PAGE_SIZE
    }

    #[verus_spec(r =>
        requires
            start_addr@ >= VADDR_UPPER_MASK,
            end_addr@ >= VADDR_UPPER_MASK,
            start_addr@ < end_addr@ <= u64::MAX,
            start_addr.pfn() % VMR_GRANULE == 0,
            end_addr.pfn() % VMR_GRANULE == 0,
            pt_flags.wf(),
            pt_flags.bits() & Pte_ALL_BITS == pt_flags.bits(),
        ensures
            r.wf(),
    )]
    pub fn new(
        start_addr: VirtAddr,
        end_addr: VirtAddr,
        pt_flags: PteFlags,
        pgtable: DekoPPtr<PageTable>,
    ) -> Self {
        proof {
            let start = start_addr@;
            let end = end_addr@;
            let start_pfn = start_addr.pfn();
            let end_pfn = end_addr.pfn();

            assert(start_pfn < end_pfn) by (bit_vector)
                requires
                    VADDR_UPPER_MASK <= start < end,
                    start_pfn == start >> 12,
                    end_pfn == end >> 12,
                    start_pfn % VMR_GRANULE == 0,
                    end_pfn % VMR_GRANULE == 0,
            ;

            assert(end_pfn <= u64::MAX / PAGE_SIZE) by (bit_vector)
                requires
                    end <= u64::MAX,
                    end_pfn == end >> 12,
            ;
        }

        proof {
            super::paging::option_page_ptr_array_size_wf();
        }

        Self {
            start_pfn: start_addr.pfn(),
            end_pfn: end_addr.pfn(),
            pt_flags,
            areas: vec![],
            pgtable,
        }
    }

    /// Inserts a new VM block [`VirtualMemory`] at the given virtual address.
    /// Note that this method checks if the block will overlap with any of the
    /// current blocks in this region.
    ///
    /// This will consumes [`VirtualMemoryRegionPermission`] since now the owner-
    /// ship has been transferred to the newly inserted block.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
            Tracked(vm_block_perm): Tracked<VirtualMemoryPermission>,
        requires
            old(self).wf(),
            old(self).wf_with(old(perm)),
            old(self).compatible_spec(&vm_block),
            old(self).nonoverlapping_block(&vm_block),
            vm_block.wf(),
        ensures
            self.wf_with(perm),
    )]
    pub fn insert_at(&mut self, vm_block: VirtualMemory) {
        let size = vm_block.range.end.0 - vm_block.range.start.0;
        let start_addr = &vm_block.range.start;
        let end_addr = &vm_block.range.end;

        // Now let's find the proper position to insert.
        let f = |mm: &VirtualMemory| -> (r: Ordering)
            requires
                mm.wf(),
            ensures
                r == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &mm.range.start.pfn(),
                    &start_addr.pfn(),
                ),
            { mm.range.start.pfn().cmp(&start_addr.pfn()) };

        proof {
            self.lemma_areas_comparator_consistent(*start_addr, f);
        }

        let idx = self.areas.binary_search_by(f);

        proof {
            assert(idx.is_err()) by {
                self.lemma_areas_non_overlap_returns_err(*start_addr, f, idx);
            }
        }

        kunimplemented!()
    }

    /// Removes the mapping from a given base address from the region.
    ///
    /// If the given address is not found then we return [`Option::None`].
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
                -> vm_perm: Tracked<Option<VirtualMemoryPermission>>,
            requires
                old(self).wf(),
                old(self).wf_with(old(perm)),
                vaddr.wf(),
                vaddr@ >= VADDR_UPPER_MASK,
    )]
    pub fn remove(&mut self, vaddr: VirtAddr) -> Option<VirtualMemory> {
        broadcast use crate::collections::group_vec_axioms;

        let pfn = vaddr.pfn();
        let f = |mm: &VirtualMemory| -> (r: Ordering)
            requires
                mm.wf(),
            ensures
                r == vstd::std_specs::cmp::OrdSpec::cmp_spec(&mm.range.start.pfn(), &pfn),
            { mm.range.start.pfn().cmp(&pfn) };

        proof {
            self.lemma_areas_comparator_consistent(vaddr, f);
        }

        match self.areas.binary_search_by(f) {
            Ok(idx) => {
                let vm = self.areas.remove(idx);

                // Then we unmap it.
                // #[verus_spec(with Tracked(&mut perm))]
                // vm.unmap(self.pgtable);

                Some(vm)
            },
            Err(_) => None,
        };

        kunimplemented!()
    }

    /// Notify the region that we have encountered a page fault at the given address.
    /// This function will return true if the page fault is handled successfully.
    ///
    /// This method does _not_ create the mapping.
    #[verus_spec(r =>
        requires
            vaddr.wf(),
    )]
    pub fn handle_page_fault(&self, vaddr: VirtAddr) -> bool {
        kunimplemented!()
    }

    /// Lemma proving that when areas are non-overlapping and we search for a new address,
    /// the binary search will return an error (indicating the address is not found).
    pub proof fn lemma_areas_non_overlap_returns_err<F>(
        &self,
        start_addr: VirtAddr,
        f: F,
        r: Result<usize, usize>,
    ) where F: FnMut(&VirtualMemory) -> Ordering
        requires
            self.wf(),
            is_sorted_spec(self.areas@),
            forall|i: int|
                #![trigger self.areas@[i]]
                0 <= i < self.areas@.len() ==> self.areas@[i].wf(),
            forall|i: int, r: Ordering|
                #![trigger self.areas@[i], f.ensures((&self.areas@[i],), r)]
                0 <= i < self.areas@.len() && f.ensures((&self.areas@[i],), r) ==> r
                    == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &self.areas@[i].range.start.pfn(),
                    &start_addr.pfn(),
                ),
            binary_search_by_spec(self.areas@, f, r),
        ensures
            r.is_err(),
    {
        broadcast use crate::collections::group_vec_axioms;
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;
        // The proof goes by contradiction: assume r.is_ok(), then we have found an index
        // where the area overlaps with the given start_addr that contradicts the non-overlapping
        // property.

        if r.is_ok() {
            let idx = r.unwrap();
            assert(0 <= idx < self.areas@.len());
            // From binary_search_by_spec postcondition for Ok case:
            // There exists ord where f.ensures((&self.areas@[idx],), ord) && ord == Equal
            // We know what ord SHOULD be from the comparator spec
            let computed_ord = vstd::std_specs::cmp::OrdSpec::cmp_spec(
                &self.areas@[idx as int].range.start.pfn(),
                &start_addr.pfn(),
            );

            // The comparator spec says f.ensures this
            assert(f.ensures((&self.areas@[idx as int],), computed_ord));

            assert(false);
        }
    }

    /// Lemma to show that the comparator used in binary search is consistent with
    /// the ordering of the areas.
    pub proof fn lemma_areas_comparator_consistent<F>(&self, start_addr: VirtAddr, f: F) where
        F: FnMut(&VirtualMemory) -> Ordering,

        requires
            self.wf(),
            is_sorted_spec(self.areas@),
            forall|i: int|
                #![trigger self.areas@[i]]
                0 <= i < self.areas@.len() ==> self.areas@[i].wf(),
            forall|i: int, r: Ordering|
                #![trigger self.areas@[i], f.ensures((&self.areas@[i],), r)]
                0 <= i < self.areas@.len() && f.ensures((&self.areas@[i],), r) ==> r
                    == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &self.areas@[i].range.start.pfn(),
                    &start_addr.pfn(),
                ),
        ensures
            comparator_consistent_spec(self.areas@, f),
    {
        broadcast use crate::collections::group_vec_axioms;
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

        assert(comparator_consistent_spec(self.areas@, f)) by {
            assert forall|i: int, j: int, ord1: Ordering, ord2: Ordering|
                0 <= i < j < self.areas@.len() && f.ensures((&self.areas@[i],), ord1) && f.ensures(
                    (&self.areas@[j],),
                    ord2,
                ) implies vstd::std_specs::cmp::OrdSpec::cmp_spec(&ord1, &ord2)
                != Ordering::Greater by {
                let area_i = &self.areas@[i];
                let area_j = &self.areas@[j];
                // From f's specification
                assert(ord1 == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &area_i.range.start.pfn(),
                    &start_addr.pfn(),
                ));
                assert(ord2 == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &area_j.range.start.pfn(),
                    &start_addr.pfn(),
                ));
                // From is_sorted_spec
                let cmp_result = vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(
                    area_i,
                    area_j,
                );
                assert(cmp_result == Some(Ordering::Less) || cmp_result == Some(Ordering::Equal));

                lemma_cmp_pivot_monotonic(
                    area_i.range.start.pfn(),
                    area_j.range.start.pfn(),
                    start_addr.pfn(),
                );
            }
        }
    }
}

#[verus_verify]
impl VirtualMemory {
    pub uninterp spec fn parent_vmm_region(&self) -> VirtualMemoryRegion;

    pub open spec fn contains_addr_spec(&self, addr: VirtAddr) -> bool {
        self.range.start@ <= addr@ < self.range.end@
    }

    pub open spec fn subset_of_spec(&self, other: &VirtualMemory) -> bool {
        &&& self.range.start@ >= other.range.start@
        &&& self.range.end@ <= other.range.end@
    }

    pub open spec fn overlap_with_spec(&self, other: &VirtualMemory) -> bool {
        &&& self.range.start@ < other.range.end@
        &&& self.range.end@ > other.range.start@
    }

    /// Checks if a given `vaddr` is contained within this virtual memory region.
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            addr.wf(),
        returns
            self.contains_addr_spec(addr),
    )]
    #[verifier::when_used_as_spec(contains_addr_spec)]
    pub fn contains_addr(&self, addr: VirtAddr) -> bool {
        addr.0 >= self.range.start.0 && addr.0 < self.range.end.0
    }

    /// Checks if this virtual memory is a subset of another virtual memory.
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            other.wf(),
        returns
            self.subset_of_spec(other),
    )]
    #[verifier::when_used_as_spec(subset_of_spec)]
    pub fn subset_of(&self, other: &VirtualMemory) -> bool {
        self.range.start.0 >= other.range.start.0 && self.range.end.0 <= other.range.end.0
    }

    /// Checks if the range is overlapped with another virtual memory.
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            other.wf(),
        returns
            self.overlap_with_spec(other),
    )]
    #[verifier::when_used_as_spec(overlap_with_spec)]
    pub fn overlap_with(&self, other: &VirtualMemory) -> bool {
        self.range.start.0 < other.range.end.0 && self.range.end.0 > other.range.start.0
    }

    /// Checks if two virtual memory regions are disjoint.
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            other.wf(),
        returns
            !self.overlap_with_spec(other),
    )]
    pub fn disjoint_with(&self, other: &VirtualMemory) -> bool {
        !self.overlap_with(other)
    }

    /// Maps this virtual memory region into the given page table.
    #[verus_spec(
        with
            Tracked(region_perm): Tracked<&mut VirtualMemoryPermission>,
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        requires
            self.wf(),
            ptr@ == self.parent_vmm_region().pgtable@,
            old(pgtable_perm).wf(),
            !old(pgtable_perm).mapped_region(self.range),
        ensures
            pgtable_perm.wf(),
            pgtable_perm.mapped_region(self.range),
    )]
    pub fn map(&self, ptr: DekoPPtr<PageTable>) {
        kunimplemented!()
    }

    /// Unmaps this virtual memory region from the given page table.
    #[verus_spec(
        with
            Tracked(region_perm): Tracked<&mut VirtualMemoryPermission>,
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        requires
            self.wf(),
            ptr@ == self.parent_vmm_region().pgtable@,
            old(pgtable_perm).wf(),
            old(pgtable_perm).mapped_region(self.range),
        ensures
            pgtable_perm.wf(),
            !pgtable_perm.mapped_region(self.range),
    )]
    pub fn unmap(&self, ptr: DekoPPtr<PageTable>) {
        kunimplemented!()
    }
}

} // verus!
