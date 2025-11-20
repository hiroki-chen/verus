use core::ops::{Range, RangeBounds};

use deko_macros::DekoDebug;
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::mm::paging::{PageTable, PageTablePermission, PteFlags, Pte_ALL_BITS};

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
    #[deko(skip)]
    pub areas: LinkedList<VirtualMemory>,
    /// The top-level page tables for this region.
    pub pgtables: Array<Option<DekoPPtr<PageTable>>, PAGE_TABLE_ENTRY>,
}

/// Tracks the corresponding permissions for a virtual memory region if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryRegionPermission {
    /// A collection of page table permissions for each top-level page table.
    pub pgtable_perms: Seq<Option<PageTablePermission>>,
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

impl WellFormed for VirtualMemoryRegion {
    open spec fn wf(&self) -> bool {
        &&& self.start_pfn < self.end_pfn
        &&& self.start_pfn % VMR_GRANULE == 0
        &&& self.end_pfn % VMR_GRANULE == 0
        &&& self.pt_flags.wf()
        &&& self.pt_flags.bits() & Pte_ALL_BITS == self.pt_flags.bits()
        &&& self.pgtable_consistent()
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

#[verus_verify]
impl VirtualMemoryRegion {
    pub open spec fn wf_with(&self, perm: &VirtualMemoryRegionPermission) -> bool {
        &&& perm.pgtable_perms.len() == self.pgtables@.len()
        &&& forall|i: int|
            #![trigger self.pgtables@[i], perm.pgtable_perms[i]]
            0 <= i < self.pgtables@.len() ==> (match self.pgtables@[i] {
                None => perm.pgtable_perms[i] == None::<PageTablePermission>,
                Some(ptr) => perm.pgtable_perms[i] matches Some(pg_perm) && ptr@
                    == pg_perm.pgtable_perm.pptr(),
            })
    }

    pub open spec fn pgtable_consistent(&self) -> bool {
        true
    }

    #[verus_spec(r =>
        requires
            start_addr@ >= VADDR_UPPER_MASK,
            end_addr@ >= VADDR_UPPER_MASK,
            start_addr@ < end_addr@,
            start_addr.pfn() % VMR_GRANULE == 0,
            end_addr.pfn() % VMR_GRANULE == 0,
            pt_flags.wf(),
            pt_flags.bits() & Pte_ALL_BITS == pt_flags.bits(),
        ensures
            r.wf(),
    )]
    pub fn new(start_addr: VirtAddr, end_addr: VirtAddr, pt_flags: PteFlags) -> Self {
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
        }

        proof {
            super::paging::option_page_ptr_array_size_wf();
        }

        Self {
            start_pfn: start_addr.pfn(),
            end_pfn: end_addr.pfn(),
            pt_flags,
            areas: LinkedList::new(),
            // This will populate later.
            pgtables: Array::fill(None),
        }
    }
}

#[verus_verify]
impl VirtualMemory {
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
}

} // verus!
