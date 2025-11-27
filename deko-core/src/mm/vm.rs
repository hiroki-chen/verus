use core::cmp::Ordering;
use core::ops::{Range, RangeBounds};

use deko_macros::DekoDebug;
use deko_std::prelude::*;
use deko_std::std_extra::cmp::{
    comparator_consistent_spec, is_sorted_spec, lemma_cmp_pivot_monotonic,
};
use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd::std_specs::cmp::*;

use super::frame_allocator::DekoAllocatorApi;
use crate::collections::Vec;
use crate::mm::paging::{
    all_in_range_paddrs, all_normalized_vaddrs, bit_not_in_addr_region, bit_not_overlapping,
    PageTable, PageTablePermission, PteFlags, Pte_ALL_BITS, PRESENT,
};
use crate::mm::vm;
use crate::{kpanic_if, kunimplemented, vec};

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
    #[deko(skip)]
    pub id: Ghost<int>,
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
    /// The mapping space this region belongs to.
    pub ms: MappingSpace,
    /// Private bit for this region.
    pub private_bit: u64,
    /// Shared bit for this region.
    pub shared_bit: u64,
}

/// Tracks the corresponding permissions for a virtual memory region if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryRegionPermission {
    pub ghost id: int,
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
    /// The physical address of this region.
    pub paddr: PhysAddr,
    /// The page table entry flags for this region.
    #[deko(skip)]
    pub flags: PteFlags,
    // The pointer to the underlying memory.
    // pub ptr: RwLockNoPred<ReprPtr<M>>, ??? possibly with some generics.
    // but this requires some transformation techniques.
}

/// Tracks the corresponding permissions for a virtual memory if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryPermission {
    pub ghost parent_id: int,
    /// Ghost state: The virtual address range this permission governs
    pub range: Range<VirtAddr>,
}

impl WellFormed for VirtualMemoryRegion {
    open spec fn wf(&self) -> bool {
        &&& self.start_pfn < self.end_pfn <= u64::MAX / PAGE_SIZE
        &&& (self.start_pfn << 12) % VMR_GRANULE == 0
        &&& (self.end_pfn << 12) % VMR_GRANULE == 0
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
        &&& self.ms.wf()
        &&& bit_not_overlapping(self.private_bit)
        &&& bit_not_in_addr_region(self.private_bit)
        &&& bit_not_overlapping(self.shared_bit)
        &&& bit_not_in_addr_region(self.shared_bit)
    }
}

impl WellFormed for VirtualMemory {
    open spec fn wf(&self) -> bool {
        &&& self.range.wf()
        &&& self.range.start@ % PAGE_SIZE == 0
        &&& self.range.end@ % PAGE_SIZE == 0
        &&& self.range.end@ + PAGE_SIZE_2M <= u64::MAX
        &&& all_normalized_vaddrs(self.range)
        &&& self.paddr@ % PAGE_SIZE == 0
        &&& self.paddr@ + (self.range.end@ - self.range.start@) < 0x000f_ffff_ffff_f000
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
        &&& self.ms == perm.pgtable_perm.mapping_space
        &&& self.private_bit == perm.pgtable_perm.private_bit
        &&& self.shared_bit == perm.pgtable_perm.shared_bit
        &&& perm.pgtable_perm.wf()
        &&& perm.pgtable_perm.pgtable_perm.pptr() == self.pgtable@
        &&& perm.vm_perms@.len() == self.areas@.len()
        &&& forall|i: int|
            0 <= i < self.areas@.len() ==> #[trigger] self.areas@[i].wf_with(&perm.vm_perms@[i])
        &&& forall|i: int|
            0 <= i < self.areas@.len() ==> #[trigger] perm.vm_perms@[i].parent_id == self.id
    }

    pub open spec fn pgtable_consistent(&self) -> bool {
        true
    }

    pub open spec fn compatible_spec(&self, vm_block: &VirtualMemory) -> bool {
        &&& vm_block.range.start@ >= self.start_pfn * PAGE_SIZE
        &&& vm_block.range.end@ <= self.end_pfn * PAGE_SIZE
        &&& all_in_range_paddrs(&self.ms, vm_block.paddr, vm_block.range)
    }

    pub open spec fn disjoint_blocks(&self, vm_block: &VirtualMemory) -> bool {
        forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int ==> { self.areas@[i].disjoint_with(vm_block) }
    }

    pub proof fn lemma_disjoint_blocks_implies_ne(&self, vm_block: &VirtualMemory)
        requires
            self.wf(),
            self.disjoint_blocks(vm_block),
            vm_block.wf(),
            vm_block.range.start@ % PAGE_SIZE == 0,
            vm_block.range.end@ % PAGE_SIZE == 0,
        ensures
            forall|i: int|
                #![trigger self.areas@[i]]
                0 <= i < self.areas@.len() as int ==> self.areas@[i].range.start.pfn()
                    != vm_block.range.start.pfn(),
    {
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

        assert forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int implies self.areas@[i].range.start.pfn()
            != vm_block.range.start.pfn() by {
            assert(!self.areas@[i].overlap_with_spec(vm_block));
            assert(self.areas@[i].range.start@ >= vm_block.range.end@ || self.areas@[i].range.end@
                <= vm_block.range.start@);
            assert(self.areas@[i].wf() && vm_block.wf());
        }
    }

    #[verus_spec(r =>
        with
            Tracked(pgtable_perm): Tracked<PageTablePermission>,
                -> vmr_perm: Tracked<VirtualMemoryRegionPermission>,
        requires
            start_addr@ >= VADDR_UPPER_MASK,
            start_addr@ < end_addr@ <= u64::MAX,
            start_addr@ % VMR_GRANULE == 0,
            end_addr@ % VMR_GRANULE == 0,
            pt_flags.wf(),
            pt_flags.bits() & Pte_ALL_BITS == pt_flags.bits(),
            ms.wf(),
            ms == pgtable_perm.mapping_space,
            private_bit == pgtable_perm.private_bit,
            shared_bit == pgtable_perm.shared_bit,
            pgtable_perm.wf(),
            pgtable_perm.pgtable_perm.pptr() == pgtable@,
            bit_not_overlapping(private_bit),
            bit_not_in_addr_region(private_bit),
            bit_not_overlapping(shared_bit),
            bit_not_in_addr_region(shared_bit),
        ensures
            r.wf(),
            r.wf_with(&vmr_perm@),
    )]
    pub fn new(
        start_addr: VirtAddr,
        end_addr: VirtAddr,
        pt_flags: PteFlags,
        pgtable: DekoPPtr<PageTable>,
        ms: MappingSpace,
        private_bit: u64,
        shared_bit: u64,
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
                    start % VMR_GRANULE == 0,
                    end % VMR_GRANULE == 0,
            ;

            assert(end_pfn <= u64::MAX / PAGE_SIZE) by (bit_vector)
                requires
                    end <= u64::MAX,
                    end_pfn == end >> 12,
            ;

            assert((((start >> 12u64) << 12u64) % VMR_GRANULE == 0) && (((end >> 12u64) << 12u64)
                % VMR_GRANULE == 0)) by (bit_vector)
                requires
                    start % VMR_GRANULE == 0,
                    end % VMR_GRANULE == 0,
                    start < end <= u64::MAX,
            ;
        }

        proof {
            super::paging::option_page_ptr_array_size_wf();
        }

        let ghost id = arbitrary();

        proof_with!(|=
            Tracked(VirtualMemoryRegionPermission {
                id,
                pgtable_perm,
                vm_perms: Ghost(Seq::empty()),
            })
        );
        Self {
            id: Ghost(id),
            start_pfn: start_addr.pfn(),
            end_pfn: end_addr.pfn(),
            pt_flags,
            areas: vec![],
            pgtable,
            ms,
            private_bit,
            shared_bit,
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
            old(self).disjoint_blocks(&vm_block),
            vm_block.wf(),
            vm_block.wf_with(&vm_block_perm),
            vm_block_perm.parent_id == old(self).id,
        ensures
            self.wf_with(perm),
    )]
    #[verifier::spinoff_prover]
    pub fn insert(&mut self, vm_block: VirtualMemory) {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

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
                self.lemma_disjoint_blocks_implies_ne(&vm_block);
            }
        }

        // Verified, but to ensure safety at runtime as well.
        kpanic_if!(
            core::intrinsics::unlikely(idx.is_ok()),
            "Trying to inserting overlapping virtual memory block into region",
        );

        let idx_unwrapped = idx.unwrap_err();
        proof {
            if idx_unwrapped < self.areas@.len() - 1 {
                assert(vm_block.range.end@ <= self.areas@[idx_unwrapped + 1].range.start@) by {
                    if vm_block.range.start@ >= self.areas@[idx_unwrapped + 1].range.end@ {
                        assert(self.areas@[idx_unwrapped + 1].range.end@ > self.areas@[idx_unwrapped
                            + 1].range.start@);
                        assert(vm_block.range.start@ > self.areas@[idx_unwrapped + 1].range.start@);
                    }
                }
            }
        }

        proof {
            perm.vm_perms = Ghost(perm.vm_perms@.insert(idx_unwrapped as int, vm_block_perm));
        }
        // We first map the new block.
        proof_with!(Tracked(perm), Ghost(idx_unwrapped as int));
        vm_block.map(self.pgtable, &self.ms, self.private_bit, self.shared_bit);
        // Finally, we can insert the new block.
        self.areas.insert(idx_unwrapped, vm_block);

    }

    /// Removes the mapping from a given base address from the region.
    ///
    /// If the given address is not found then we return [`Option::None`].
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
                -> vm_perm: Ghost<Option<VirtualMemoryPermission>>,
            requires
                old(self).wf(),
                old(self).wf_with(old(perm)),
                vaddr.wf(),
                vaddr@ >= VADDR_UPPER_MASK,
            ensures
                self.wf_with(perm),
                r matches Some(vm) ==> {
                    &&& vm.wf()
                    &&& vm_perm@ matches Some(vm_perm_val) && vm.wf_with(&vm_perm_val) && vm_perm_val.parent_id == self.id
                }
    )]
    pub fn remove(&mut self, vaddr: VirtAddr) -> Option<VirtualMemory> {
        broadcast use vstd::std_specs::vec::group_vec_axioms;

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

                // Then we unmap it; remove it.
                // #[verus_spec(with Tracked(&mut perm))]
                // vm.unmap(self.pgtable);

                let ghost vm_perm = perm.vm_perms@.index(idx as int);

                proof {
                    // remove it.
                    perm.vm_perms = Ghost(perm.vm_perms@.remove(idx as int));
                }

                proof_with!(|= Ghost(Some(vm_perm)));
                Some(vm)
            },
            Err(_) => {
                proof_with!(|= Ghost(None));
                None
            },
        }
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
        broadcast use vstd::std_specs::vec::group_vec_axioms;
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
    pub open spec fn wf_with(&self, perm: &VirtualMemoryPermission) -> bool {
        &&& self.range == perm.range
    }

    pub open spec fn contains_addr_spec(&self, addr: VirtAddr) -> bool {
        self.range.start@ <= addr@ < self.range.end@
    }

    pub open spec fn subset_of_spec(&self, other: &VirtualMemory) -> bool {
        &&& self.range.start@ >= other.range.start@
        &&& self.range.end@ <= other.range.end@
    }

    pub open spec fn overlap_with_spec(&self, other: &VirtualMemory) -> bool {
        !self.disjoint_with_spec(other)
    }

    pub open spec fn disjoint_with_spec(&self, other: &VirtualMemory) -> bool {
        self.range.end@ <= other.range.start@ || self.range.start@ >= other.range.end@
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
    ///
    /// [       ]
    ///     [        ]
    /// [       ]
    ///    []
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
        !self.disjoint_with(other)
    }

    /// Checks if two virtual memory regions are disjoint.
    ///
    /// [     ] [      ]
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            other.wf(),
        returns
            self.disjoint_with_spec(other),
    )]
    #[verifier::when_used_as_spec(disjoint_with_spec)]
    pub fn disjoint_with(&self, other: &VirtualMemory) -> bool {
        self.range.end.0 <= other.range.start.0 || self.range.start.0 >= other.range.end.0
    }

    /// Maps this virtual memory region into the given page table.
    #[verus_spec(
        with
            Tracked(parent_perm): Tracked<&mut VirtualMemoryRegionPermission>,
            Ghost(idx): Ghost<int>,
        requires
            self.wf(),
            self.wf_with(&old(parent_perm).vm_perms@.index(idx)),
            ptr@ == old(parent_perm).pgtable_perm.pgtable_perm.pptr(),
            old(parent_perm).pgtable_perm.wf(),
            old(parent_perm).pgtable_perm.mapping_space == ms,
            old(parent_perm).pgtable_perm.private_bit == private_bit,
            old(parent_perm).pgtable_perm.shared_bit == shared_bit,
            ms.wf(),
            bit_not_overlapping(private_bit),
            bit_not_in_addr_region(private_bit),
            bit_not_overlapping(shared_bit),
            bit_not_in_addr_region(shared_bit),
            all_in_range_paddrs(ms, self.paddr, self.range),
        ensures
            parent_perm.pgtable_perm.wf(),
            parent_perm.pgtable_perm.mapped_region(self.range),
            parent_perm.pgtable_perm.mapping_space == ms,
            parent_perm.pgtable_perm.private_bit == private_bit,
            parent_perm.pgtable_perm.shared_bit == shared_bit,
            parent_perm.pgtable_perm.pgtable_perm.pptr() == old(parent_perm).pgtable_perm.pgtable_perm.pptr(),
            parent_perm.vm_perms == old(parent_perm).vm_perms,
    )]
    pub fn map(
        &self,
        ptr: DekoPPtr<PageTable>,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) {
        broadcast use crate::mm::paging::PteFlags::lemma_each_bit_is_valid;

        let flags = PteFlags::from_bits_truncate(self.flags.bits() | PRESENT);

        proof {
            assert(flags.bits() & Pte_ALL_BITS == flags.bits() && flags.wf()) by {
                bit_u64_and_auto();
            }
        }

        PageTable::map_page_multiple(
            ptr,
            self.range.clone(),
            self.paddr,
            flags,
            ms,
            private_bit,
            shared_bit,
            Tracked(&mut parent_perm.pgtable_perm),
        );
    }

    /// Unmaps this virtual memory region from the given page table.
    #[verus_spec(
        with
            Tracked(region_perm): Tracked<&mut VirtualMemoryPermission>,
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        requires
            self.wf(),
            self.wf_with(old(region_perm)),
            ptr@ == old(pgtable_perm).pgtable_perm.pptr(),
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
