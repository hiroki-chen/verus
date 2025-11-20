use deko_macros::DekoDebug;
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::mm::paging::PteFlags;

verus! {

/// Granularity of ranges mapped by [`VirtualMemoryRegion`]. The mapped region of a
/// [`VirtualMemoryRegion`] is always a multiple of this constant.
/// One [`VMR_GRANULE`] covers one top-level page-table entry on x86-64 with
/// 4-level paging.
pub const VMR_GRANULE: u64 = PAGE_SIZE * 512 * 512 * 512;

/// This struct manages the mappings in a region of the virtual address space.
#[derive(DekoDebug)]
pub struct VirtualMemoryRegion {
    /// Start address of this range as virtual PFN (VirtAddr >> PAGE_SHIFT).
    pub start_pfn: u64,
    /// End address of this range as virtual PFN (VirtAddr >> PAGE_SHIFT)
    pub end_pfn: u64,
    /// Global to all mappings in this virtual memory region.
    #[deko(skip)]
    pub pt_flags: PteFlags,
}

impl WellFormed for VirtualMemoryRegion {
    open spec fn wf(&self) -> bool {
        &&& self.start_pfn < self.end_pfn
        &&& self.start_pfn % VMR_GRANULE == 0
        &&& self.end_pfn % VMR_GRANULE == 0
    }
}

#[verus_verify]
impl VirtualMemoryRegion {
    #[verus_spec(r =>
        requires
            start_addr@ >= VADDR_UPPER_MASK,
            end_addr@ >= VADDR_UPPER_MASK,
            start_addr@ < end_addr@,
            start_addr.pfn() % VMR_GRANULE == 0,
            end_addr.pfn() % VMR_GRANULE == 0,
        ensures
            r.wf(),
    )]
    pub fn new(start_addr: VirtAddr, end_addr: VirtAddr, pt_flags: PteFlags) -> Self {
        proof {

            let start = start_addr@;
            let end = end_addr@;
            let start_pfn= start_addr.pfn();
            let end_pfn = end_addr.pfn();

            assert(start_pfn < end_pfn) by (bit_vector)
                requires
                    VADDR_UPPER_MASK <= start < end,
                    start_pfn == start >> 12,
                    end_pfn == end >> 12,
                    start_pfn % VMR_GRANULE == 0,
                    end_pfn % VMR_GRANULE == 0
                ;
        }

        Self { start_pfn: start_addr.pfn(), end_pfn: end_addr.pfn(), pt_flags }
    }
}

} // verus!
