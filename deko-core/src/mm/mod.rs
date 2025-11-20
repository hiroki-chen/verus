//! This module implements the memory subsystem for the Deko monitor.
//!
//! The layout of the memory is as follows:
//!
//! - Buddy allocator that manages the raw, untyped physical memory.
//! - Kernel page frame allocator that allocates physical pages.
//! - Some high level allocators that allocates pages from the page frame allocators.
//! - A memory manager that manages the page tables and memory regions.
pub mod frame_allocator;
pub mod paging;
pub mod vm;

use core::ops::Range;

use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::kerror;
use crate::mm::frame_allocator::DekoPageFrameAllocator;
use crate::mm::paging::{PageTable, PageTablePermission, PteFlags};

verus! {

pub exec static DEKO_MAPPING_SPACE: OnceCell<MappingSpace, MappingSpacePred>
    ensures
        DEKO_MAPPING_SPACE.wf(),
{
    OnceCell::new(Ghost(MappingSpacePred {  }))
}

pub exec static DEKO_FRAME_ALLOCATOR: DekoPageFrameAllocator
    ensures
        DEKO_FRAME_ALLOCATOR.wf(),
{
    DekoPageFrameAllocator::new()
}

pub exec static PTE_MASK_PRIVATE: OnceCellNoPred<u64>
    ensures
        PTE_MASK_PRIVATE.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub exec static PTE_MASK_SHARED: OnceCellNoPred<u64>
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

pub exec static MAX_PHYS_ADDR: OnceCellNoPred<u64>
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
    pub private_pte_mask: u64,
    pub shared_pte_mask: u64,
    pub addr_mask_width: u32,
    pub phys_addr_sizes: u32,
}

/// This function initializes the global `DEKO_FRAME_ALLOCATOR` with the given
/// physical memory region for physical memory allocation.
#[verus_spec(r =>
    requires
        heap_start.wf(),
        heap_end.wf(),
        heap_start@ % 0x1000 == 0,
        heap_end@ % 0x1000 == 0,
        heap_end@ > heap_start@,
        valid_heap_param(heap_start.0, (heap_end.0 - heap_start.0) as u64, HEAP_SIZE as u64),
        heap_start == VirtAddr::new_spec(STAGE2_HEAP_START as u64),
        heap_end == VirtAddr::new_spec(STAGE2_HEAP_END as u64),
)]
pub fn init_frame_allocator(heap_start: &VirtAddr, heap_end: &VirtAddr) {
    let phys_start = PhysAddr(heap_start.0);

    DEKO_FRAME_ALLOCATOR.init(phys_start.0, heap_end.0 - heap_start.0);
}

#[inline(always)]
pub fn virt_to_phys(
    private_bit: u64,
    shared_bit: u64,
    vaddr: VirtAddr,
    Tracked(pgtable_perm): Tracked<&PageTablePermission>,
) -> (paddr: PhysAddr)
    requires
        private_bit == pgtable_perm.private_bit,
        shared_bit == pgtable_perm.shared_bit,
        pgtable_perm.wf(),
        vaddr.wf(),
    ensures
        paddr.wf(),
{
    match PageTable::virt_to_frame(vaddr, private_bit, Tracked(pgtable_perm)) {
        Some(v) => v.address(private_bit, shared_bit),
        None => {
            crate::die("virt_to_phys: address not mapped");
        },
    }
}

#[inline(always)]
pub fn phys_to_virt(
    ctx: DekoPPtr<DekoCpuCtx>,
    Tracked(ctx_perm): Tracked<&DekoCpuCtxPermission>,
    paddr: PhysAddr,
) -> (vaddr: VirtAddr)
    requires
        paddr.wf(),
        ctx_perm.wf_with(ctx),
        ctx_perm.ptr_perm.value().kernel_mapping().kernel.in_range_spec(paddr)
            || ctx_perm.ptr_perm.value().kernel_mapping().physmap.in_range_spec(paddr),
    ensures
{
    match ctx.borrow(Tracked(&ctx_perm.ptr_perm)).kernel_mapping().phys_to_virt(paddr) {
        Some(v) => v,
        None => {
            kerror!("phys_to_virt: address not mapped");
            crate::die("phys_to_virt: address not mapped");
        },
    }
}

pub tracked struct DekoMemoryRegionPermission;

impl DekoMemoryRegionPermission {
    /// Check if the permission is well-formed.
    pub open spec fn wf(&self) -> bool {
        true
        // TODO: Implement me!

    }
}

/// A continuous memory region.
pub struct DekoMemoryRegion {
    /// The physical start address of the memory region.
    pub phys_start: PhysAddr,
    /// The virtual start address of the memory region.
    pub virt_start: VirtAddr,
    /// The number of pages in the memory region.
    pub npages: u64,
    /// The permission of the memory region.
    pub perm: Tracked<DekoMemoryRegionPermission>,
}

impl WellFormed for DekoMemoryRegion {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.phys_start.wf()
        &&& self.virt_start.wf()
        &&& self.npages > 0
        &&& self.npages <= (u64::MAX / 0x1000)
        &&& self.phys_start@ % 0x1000 == 0
        &&& self.virt_start@ % 0x1000 == 0
        &&& self.perm@.wf()
        &&& self.virt_start@ + self.npages * 0x1000 <= u64::MAX
    }
}

impl DekoMemoryRegion {
    #[verifier::inline]
    pub open spec fn contains_addr_spec(&self, addr: VirtAddr) -> bool {
        &&& addr@ >= self.virt_start@
        &&& addr@ < self.virt_start@ + self.npages * 0x1000
    }

    #[verifier::inline]
    pub open spec fn subset_of_spec(&self, other: &DekoMemoryRegion) -> bool {
        &&& self.virt_start@ >= other.virt_start@
        &&& self.virt_start@ + self.npages * 0x1000 <= other.virt_start@ + other.npages * 0x1000
    }

    #[verifier::inline]
    pub open spec fn overlap_with_spec(&self, other: &DekoMemoryRegion) -> bool {
        &&& self.virt_start@ < other.virt_start@ + other.npages * 0x1000
        &&& self.virt_start@ + self.npages * 0x1000 > other.virt_start@
    }

    #[verifier::inline]
    pub open spec fn empty_spec(&self) -> bool {
        &&& self.npages == 0
    }

    #[verifier::when_used_as_spec(contains_addr_spec)]
    #[inline]
    pub fn contains_addr(&self, addr: VirtAddr) -> (r: bool)
        requires
            self.wf(),
            addr.wf(),
        ensures
            self.contains_addr_spec(addr) == r,
    {
        addr.0 >= self.virt_start.0 && addr.0 < self.virt_start.0 + self.npages * 0x1000
    }

    #[verifier::when_used_as_spec(subset_of_spec)]
    #[inline]
    pub fn subset_of(&self, other: &DekoMemoryRegion) -> (r: bool)
        requires
            self.wf(),
            other.wf(),
        ensures
            self.subset_of_spec(other) == r,
    {
        self.virt_start.0 >= other.virt_start.0 && self.virt_start.0 + self.npages * 0x1000
            <= other.virt_start.0 + other.npages * 0x1000
    }

    #[verifier::when_used_as_spec(overlap_with_spec)]
    #[inline]
    pub fn overlap_with(&self, other: &DekoMemoryRegion) -> (r: bool)
        requires
            self.wf(),
            other.wf(),
        ensures
            self.overlap_with_spec(other) == r,
    {
        self.virt_start.0 < other.virt_start.0 + other.npages * 0x1000 && self.virt_start.0
            + self.npages * 0x1000 > other.virt_start.0
    }

    #[verifier::when_used_as_spec(empty_spec)]
    #[inline]
    pub fn empty(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            self.empty_spec() == r,
    {
        self.npages == 0
    }

    #[verifier::external_body]
    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
            r.empty_spec(),
    {
        DekoMemoryRegion {
            phys_start: PhysAddr(0),
            virt_start: VirtAddr::new(0),
            npages: 0,
            perm: Tracked::assume_new(),
        }
    }

    pub fn init_mem_region(&mut self, phys_start: PhysAddr, virt_start: VirtAddr, npages: u64) {
    }
}

/// This function copies memory from one ELF segment to another.
///
/// # Safety
///
/// The caller must ensure that the source and destination memory regions are valid and do not overlap.
#[verifier::external_body]
#[verus_spec(r =>
    requires
        true,
)]
pub unsafe fn copy_elf_mem(seg: Range<VirtAddr>) {
}

} // verus!
