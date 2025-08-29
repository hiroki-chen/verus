pub mod paging;

use deko_std::sync::OnceCellNoPred;
use vstd::prelude::*;

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

} // verus!
