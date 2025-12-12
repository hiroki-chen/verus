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
pub mod stack;
pub mod vm;

use core::ops::Range;

use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::frame_allocator::DekoPageFrameAllocator;
use crate::mm::paging::{PageTable, PageTablePermission, PteFlags};
use crate::{kerror, DekoKernelLaunchInfo};

verus! {

struct Allocator;

/// Forbidden global allocator implementation to avoid accidental usage.
///
/// If you really want to use heap allocator for [`alloc`] crate, please use
/// explicit APIs like [`alloc::vec::Vec::new_in`] with a proper allocator
/// such as [`DekoHeapAllocator`].
#[verifier::external]
unsafe impl core::alloc::GlobalAlloc for Allocator {
    unsafe fn alloc(&self, _layout: core::alloc::Layout) -> *mut u8 {
        panic!("No global allocator configured; please use explicit allocators like DekoHeapAllocator.");
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {
        panic!("No global allocator configured; please use explicit allocators like DekoHeapAllocator.");
    }
}

#[cfg(feature = "global_alloc_api")]
#[verifier::external]
#[global_allocator]
static GLOBAL_ALLOCATOR: Allocator = Allocator;

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

pub exec static PTE_MASK_PRIVATE: DekoSimpleOnceCell<u64>
    ensures
        PTE_MASK_PRIVATE.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub exec static PTE_MASK_SHARED: DekoSimpleOnceCell<u64>
    ensures
        PTE_MASK_SHARED.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub exec static PHYS_ADDR_SIZE: DekoSimpleOnceCell<u32>
    ensures
        PHYS_ADDR_SIZE.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub exec static MAX_PHYS_ADDR: DekoSimpleOnceCell<u64>
    ensures
        MAX_PHYS_ADDR.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub exec static FEATURE_MASK: DekoSimpleOnceCell<PteFlags>
    ensures
        FEATURE_MASK.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
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

pub fn virt_to_phys_checked(
    private_bit: u64,
    shared_bit: u64,
    vaddr: VirtAddr,
    Tracked(pgtable_perm): Tracked<&PageTablePermission>,
) -> (paddr: Option<PhysAddr>)
    requires
        private_bit == pgtable_perm.private_bit,
        shared_bit == pgtable_perm.shared_bit,
        pgtable_perm.wf(),
        vaddr.wf(),
    ensures
        paddr.wf(),
        paddr matches Some(paddr) ==> {
            &&& pgtable_perm.virt_to_frame_spec(vaddr) matches Some(frame) && paddr@
                == frame.address_spec(private_bit, shared_bit)@ & !0xfff
            &&& paddr@ % PAGE_SIZE == 0
        },
{
    match PageTable::virt_to_frame(vaddr, private_bit, Tracked(pgtable_perm)) {
        Some(v) => {
            let v = v.address(private_bit, shared_bit);

            proof {
                let v = v@;
                assert((v & !0xfff) % PAGE_SIZE == 0) by (bit_vector);
            }

            Some(PhysAddr(v.0 & !0xfff))
        },
        None => { None },
    }
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
        pgtable_perm.virt_to_frame_spec(vaddr) matches Some(frame) && paddr@ == frame.address_spec(
            private_bit,
            shared_bit,
        )@ & !0xfff,
        paddr@ % PAGE_SIZE == 0,
{
    match PageTable::virt_to_frame(vaddr, private_bit, Tracked(pgtable_perm)) {
        Some(v) => {
            let v = v.address(private_bit, shared_bit);

            proof {
                let v = v@;
                assert((v & !0xfff) % PAGE_SIZE == 0) by (bit_vector);
            }

            PhysAddr(v.0 & !0xfff)
        },
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

/// This function initializes the global memory mapping.
#[verus_spec(
    with
        Tracked(ctx_perm): Tracked<&DekoCpuCtxPermission>,
    requires
        header.wf(),
        ctx_perm.wf(),
)]
pub fn init_memory_map(header: &DekoKernelLaunchInfo) {
    // stub: placeholder.
}

/// Since we are now in a full-fledged system, bootstrapped memory regions
/// used during early boot should be invalidated to prevent accidental usage
/// and for more memory to be available for general allocation.
#[verus_spec(
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(ctx_perm).wf_with(ctx),
        header.wf(),
)]
pub fn invalidate_boot_mem(ctx: DekoPPtr<DekoCpuCtx>, header: &DekoKernelLaunchInfo) {
    // stub: placeholder.
    // Always invalidate stage 2 boot memory unless the firmware
    // is loaded into the low memory.
}

} // verus!
