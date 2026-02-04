//! This module implements the memory subsystem for the Deko monitor.
//!
//! The layout of the memory is as follows:
//!
//! - Buddy allocator that manages the raw, untyped physical memory.
//! - Kernel page frame allocator that allocates physical pages.
//! - Some high level allocators that allocates pages from the page frame allocators.
//! - A memory manager that manages the page tables and memory regions.
pub mod bounce_buffer;
#[cfg(feature = "alloc")]
pub mod frame_allocator;
pub mod paging;
pub mod stack;
pub mod vm;

use core::ops::Range;

use deko_std::prelude::*;
use vstd::invariant;
use vstd::prelude::*;

use crate::collections::Vec;
use crate::cpu::irq::IrqUnSafeLockGuard;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::imp::{page_state_change, PageStateChangeOp};
use crate::mm::frame_allocator::DekoPageFrameAllocator;
use crate::mm::paging::{PageTable, PageTablePermission, PteFlags};
use crate::mm::vm::TempMapping;
use crate::{kerror, kinfo, kpanic_if, kwarn, vec, DekoKernelLaunchInfo};

verus! {

/// This bookkeeps the global memory maps for physical memory regions, i.e.,
/// valid memories that can be used system-wide.
#[doc(hidden)]
exec static GUEST_MMAP: DekoSimpleOnceCell<Vec<PaddrRange>>
    ensures
        GUEST_MMAP.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

/// This function populates [`GUEST_MMAP`] with the initial memory regions provided
/// by the bootloader.
///
/// This does not check if the memory is overlapping with the kernel itself.
#[verifier::spinoff_prover]
#[verus_spec(
    requires
        igvm_params.wf(),
)]
pub fn init_mmap(igvm_params: &IgvmParams<'_>) {
    if GUEST_MMAP.get().is_some() {
        // Already initialized.
        return ;
    }
    // Now parse the memory map from the header.

    let mut regions = vec![];
    let mut number_of_entries = 0;
    let mut next_page_number = 0;

    // Count the number of valid memory entries.
    let mut i = 0;
    #[verus_spec(
        invariant
            0 <= number_of_entries <= i <= 0xAA,
            igvm_params.wf(),
        decreases
            0xAA - i,
    )]
    while i < 0xAA {
        proof {
            assert(0 <= i < 0xAA);
        }
        let entry = &igvm_params.igvm_memory_map.memory_map[i];

        if entry.number_of_pages == 0 {
            break ;
        }
        kpanic_if!(
            entry.starting_gpa_page_number < next_page_number,
            "init_mmap: overlapping or unsorted memory map entries"
        );

        let next_supplied_page_number = entry.starting_gpa_page_number.wrapping_add(
            entry.number_of_pages,
        );

        kpanic_if!(
            next_supplied_page_number < next_page_number,
            "init_mmap: overlapping memory map entries"
        );
        next_page_number = next_supplied_page_number;
        number_of_entries += 1;
        i += 1;
    }

    kinfo!("init_mmap: found", number_of_entries => hex, "memory map entries");

    // Now populate the regions.
    for i in 0..number_of_entries as usize
        invariant
            0 <= i <= number_of_entries <= 0xAA,
            igvm_params.wf(),
            regions@.len() <= i as int,
    {
        proof {
            assert(0 <= i < 0xAA);
        }
        let entry = &igvm_params.igvm_memory_map.memory_map[i];

        if matches!(entry.entry_type, MemoryMapEntryType::MEMORY) {
            let starting_page = entry.starting_gpa_page_number as u64;
            let number_of_pages = entry.number_of_pages as u64;

            regions.push(
                PhysAddr(starting_page.wrapping_mul(PAGE_SIZE))..PhysAddr(
                    ((starting_page.wrapping_add(number_of_pages)).wrapping_mul(PAGE_SIZE)),
                ),
            );
        }
    }

    kinfo!("Guest memory regions:");
    for i in 0..regions.len() {
        let region = &regions[i];
        kinfo!("  Region", i => dec, ":", region.start.0 => hex, "-", region.end.0 => hex);
    }

    GUEST_MMAP.init(regions);
}

/// Checks if the given physical address is within any of the guest memory regions.
///
/// This sanity check is important when checking if the guest provides us with the
/// valid physical addresses for various operations (like page validations).
pub fn check_within_guest_mmap(paddr: PhysAddr) -> bool {
    match GUEST_MMAP.get() {
        Some(regions) => {
            for i in 0..regions.len() {
                let region = &regions[i];
                if region.start.0 <= paddr.0 && paddr.0 < region.end.0 {
                    return true;
                }
            }

            false
        },
        None => {
            kwarn!("check_within_guest_mmap: `GUEST_MMAP` not initialized");
            false
        },
    }
}

/// This slightly differs from [`init_mmap`] as this will also inserts mappings
/// collected from IGVM parameters into the guest physical memory regions.
#[verus_spec(
    requires
        igvm_params.wf(),
)]
pub fn init_guest_mmap(igvm_params: &IgvmParams<'_>) {
    kinfo!("init_guest_mmap: initializing guest memory map");

    let mmap_count = igvm_params.igvm_param_block.firmware.memory_map_page_count;
    let mmap_addr = igvm_params.igvm_param_block.firmware.memory_map_page;
    let mmap_prevalidated = igvm_params.igvm_param_block.firmware.mmap_prevalidated;
    let need_psc = igvm_params.igvm_param_page.environment_info & 0x1 != 0;

    // If no extra memory mappings, return early.
    if mmap_count != 0 {
        // Now we read the memory map entries.
        let mmap_paddr = PhysAddr(mmap_addr as u64);
        let mmap_region = mmap_paddr..PhysAddr(mmap_addr as u64 + mmap_count as u64);  // no overflow checks needed as u32 cannot overflow u64
        kinfo!("init_guest_mmap: added guest memory map region:", mmap_region);

        let Some(temp_mm_mapping) = TempMapping::new(mmap_region.clone()) else {
            kerror!("init_guest_mmap: failed to create temp mapping for mmap region");
            return ;
        };

        // Will be used for rmpadjust/pvalidate operations.
        let mmap_va = temp_mm_mapping.inner.start;
        if mmap_prevalidated == 0 {
            if need_psc {
                // do a pre-validation of the memory map entries.
                page_state_change(mmap_region, PageStateChangeOp::Private);

            }
        }
        // TODO: FILL ME.

    }
}

/// Dummy allocator type to prevent accidental usage of the global allocator.
#[doc(hidden)]
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

pub exec static DEKO_FRAME_ALLOCATOR: DekoPageFrameAllocator<HEAP_SIZE_STAGE2>
    ensures
        DEKO_FRAME_ALLOCATOR.wf(),
{
    DekoPageFrameAllocator::new()
}

pub exec static DEKO_FRAME_ALLOCATOR_FULL: DekoPageFrameAllocator<HEAP_SIZE_FULL>
    ensures
        DEKO_FRAME_ALLOCATOR_FULL.wf(),
{
    DekoPageFrameAllocator::new()
}

pub exec static DEKO_IFC_FRAME_ALLOCATOR: DekoSimpleOnceCell<DekoPageFrameAllocator<10>>
    ensures
        DEKO_IFC_FRAME_ALLOCATOR.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
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
        valid_heap_param(heap_start.0, (heap_end.0 - heap_start.0) as u64, HEAP_SIZE_STAGE2 as u64),
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

/// This function translates a virtual address to a physical address
/// using the given page table permission.
///
/// This does NOT add back the page offset, so the caller should
/// handle that if necessary.
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

pub fn dump_frame_allocator_usage() -> u64 {
    DEKO_FRAME_ALLOCATOR_FULL.0.remaining()
}

#[verifier::external_body]
#[verus_spec(
    requires
        paddr.wf(),
        paddr@ % PAGE_SIZE == 0,
)]
#[inline(always)]
pub fn zero_page(paddr: VirtAddr, len: usize) {
    // SAFETY: Caller must ensure that the physical address is valid and page-aligned.
    unsafe {
        let ptr = paddr.0 as *mut u8;
        core::ptr::write_bytes(ptr, 0, len * PAGE_SIZE as usize);
    }
}

} // verus!
