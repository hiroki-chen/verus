pub mod paging;

use deko_std::prelude::*;
use vstd::prelude::*;

use crate::address::{PhysAddr, VirtAddr};
use crate::mm::paging::PteFlags;

verus! {

pub exec static PTE_MASK_PRIVATE: OnceCellNoPred<usize>
    ensures
        PTE_MASK_PRIVATE.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub exec static PTE_MASK_SHARED: OnceCellNoPred<usize>
    ensures
        PTE_MASK_SHARED.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub exec static PHYS_ADDR_SIZE: OnceCellNoPred<u32>
    ensures
        PHYS_ADDR_SIZE.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub exec static MAX_PHYS_ADDR: OnceCellNoPred<usize>
    ensures
        MAX_PHYS_ADDR.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub exec static FEATURE_MASK: OnceCellNoPred<PteFlags>
    ensures
        FEATURE_MASK.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub struct PageEncryptionMasks {
    pub private_pte_mask: usize,
    pub shared_pte_mask: usize,
    pub addr_mask_width: u32,
    pub phys_addr_sizes: u32,
}

pub fn init_heap_allocator(heap_start: &VirtAddr, heap_end: &VirtAddr)
    requires
        heap_start.wf(),
        heap_end.wf(),
        heap_start@ % 0x1000 == 0,
        heap_end@ % 0x1000 == 0,
        heap_end@ > heap_start@,
        valid_heap_param(heap_start.0, (heap_end.0 - heap_start.0) as u64, HEAP_SIZE as u64),
{
    let phys_start = PhysAddr(heap_start.0);

    DEKO_ALLOCATOR.init(phys_start.0, heap_end.0 - heap_start.0);
}

} // verus!
