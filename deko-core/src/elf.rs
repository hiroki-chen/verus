//! ELF File Parsing and Loading Module
//!
//! This module provides trusted wrapper types and functionality for parsing and loading
//! ELF (Executable and Linkable Format) files within the Deko secure monitor system.
//! Built on top of the external `elf` crate, it integrates ELF handling capabilities
//! with Verus formal verification framework to ensure memory safety and correctness.
//!
//! ## Core Components
//!
//! The module centers around two main wrapper types:
//! - [`ElfFile`]: A trusted wrapper around `Elf64File` that represents a complete ELF binary
//! - [`ElfLoadSegement`]: A wrapper for individual ELF load segments with address validation
//!
//! ## Key Functionality
//!
//! - **ELF File Creation**: Safe construction from physical memory ranges with alignment validation
//! - **Segment Loading**: Iterative loading of ELF segments into virtual memory with proper bounds checking
//! - **Address Management**: Virtual address calculations and range validation for higher-half kernel mappings
//! - **Well-Formedness**: Formal specifications ensuring ELF files and segments meet safety requirements
//!
//! ## Safety and Verification
//!
//! The module uses `#[verifier::external_body]` annotations for interfacing with the
//! unverified external ELF parsing library while maintaining verification guarantees
//! at the boundary through pre- and post-conditions.
//!
//! ## Non goals
//!
//! We do not intend to verify any functionality related to ELF parsing itself although
//! it is beneficial to do so in the future.
use core::ops::Range;

use deko_std::prelude::*;
use elf::Elf64ImageLoadSegment;
use vstd::prelude::*;
use vstd::{bytes, invariant};

use crate::cpu::DekoCpuCtxPermission;
use crate::{log_hex_dump, log_hex_prefixed, log_int, log_str, log_str_ln};

verus! {

#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>
    requires
        segment.wf(),
        paddr.wf(),
        header.wf(),
    ensures
        r.2@ >= r.1@,
        /* Non overflowing properties... */
)]
fn load_elf_segment(segment: ElfLoadSegement, paddr: PhysAddr, header: Stage2LaunchInfo) -> (r: (
    PhysAddr,
    VirtAddr,
    VirtAddr,
)) {
    // Find the segment's bounds
    // All ELF segments should be aligned to the page size. If not, there's
    // the risk of pvalidating a page twice, bail out if so. Note that the
    // ELF reading code had already verified that the individual segments,
    // with bounds specified as in the ELF file, are non-overlapping.
    let segment_start = segment.vaddr_range().start;
    let segment_end = segment.vaddr_range().end.page_align_up();
    let segment_len = segment_end.0 - segment_start.0;

    log_str!("Mapping ELF segment: [");
    log_hex_prefixed!(segment_start.0);
    log_str!(" - ");
    log_hex_prefixed!(segment_end.0);
    log_str_ln!("]");

    // Although we've checked in the spec that the segment start is page-aligned,
    // double-check here to avoid any risk just to ensure safety.
    if core::intrinsics::unlikely(segment_start.0 % PAGE_SIZE != 0) {
        proof {
            assert(false);
        }

        crate::die("ELF segment virtual address not page-aligned!");
    }
    // Note that here wo have to map and validate the memory

    #[verus_spec(with Tracked(ctx_perm))]
    crate::mm::paging::map_and_validate_elf_segment(header, segment_start, segment_end, paddr);

    crate::die("Not implemented yet")
}

/// A thin wrapper around [`elf::Elf64File`] to be used in Verus code.
///
/// Note that for the time being we do not intend to verify any functionality
/// related to ELF parsing. Thus, this struct only serves as a marker type
/// to allow us to pass ELF files around in Verus code.
#[verifier::external_body]
pub struct ElfFile<'a>(elf::Elf64File<'a>);

#[verifier::external_body]
pub struct ElfLoadSegement<'a>(Elf64ImageLoadSegment<'a>);

impl<'a> WellFormed for ElfFile<'a> {
    /// Also see [`xmas_elf::header::sanity_check`].
    open spec fn wf(&self) -> bool {
        let segments = self.load_segments();

        forall|i: int| 0 <= i < segments.len() ==> (#[trigger] segments[i]).wf()
    }
}

impl<'a> WellFormed for ElfLoadSegement<'a> {
    open spec fn wf(&self) -> bool {
        // The build system should ensure that the segment
        // virtual address range is at higher half.
        &&& self.vaddr_end()@ >= self.vaddr_begin()@ >= VADDR_UPPER_MASK
        &&& self.vaddr_end()@ + PAGE_SIZE - 1 < u64::MAX
        &&& self.vaddr_begin()@ % PAGE_SIZE == 0  // begin is aligned.

    }
}

impl<'a> ElfFile<'a> {
    pub uninterp spec fn get_vaddr_alloc_base_spec(&self) -> VirtAddr;

    #[verifier::inline]
    pub open spec fn load_segment_num_spec(&self, base: VirtAddr) -> usize {
        self.load_segments().len() as usize
    }

    #[verifier::inline]
    pub open spec fn segment_in_loaded_range_spec(
        &self,
        segment: ElfLoadSegement,
        base: VirtAddr,
    ) -> bool {
        self.load_segments().contains(segment)
    }

    pub uninterp spec fn load_segments(&self) -> Seq<ElfLoadSegement>;

    /// Creates a new `ElfFile` from the given byte slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the provided byte slice is a valid ELF file.
    #[verifier::external_body]
    pub fn new(start_paddr: PhysAddr, end_paddr: PhysAddr) -> (r: Option<Self>)
        requires
            start_paddr@ % 0x1000 == 0,
            end_paddr@ % 0x1000 == 0,
            start_paddr@ <= end_paddr@ <= u32::MAX,
            start_paddr.wf(),
            end_paddr.wf(),
        ensures
            r matches Some(r) ==> r.wf(),
    {
        let bytes = unsafe {
            core::slice::from_raw_parts(
                start_paddr.0 as *const u8,
                (end_paddr.0 - start_paddr.0) as usize,
            )
        };

        Some(Self(elf::Elf64File::read(bytes).ok()?))
    }

    #[inline]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(get_vaddr_alloc_base_spec)]
    pub fn get_vaddr_alloc_base(&self) -> (r: VirtAddr)
        requires
            self.wf(),
        ensures
            r == self.get_vaddr_alloc_base_spec(),
    {
        self.0.image_load_vaddr_alloc_info().range.vaddr_begin.into()
    }

    #[inline]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(load_segment_num_spec)]
    pub fn load_segment_num(&self, base: VirtAddr) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.load_segment_num_spec(base),
    {
        self.0.image_load_segment_iter(base.0).count()
    }

    #[verifier::external_body]
    pub fn get_segment(&self, index: usize, base: VirtAddr) -> (r: ElfLoadSegement)
        requires
            self.wf(),
            index < self.load_segment_num_spec(base),
        ensures
            r == self.load_segments()[index as int],
    {
        ElfLoadSegement(self.0.image_load_segment_iter(0).nth(index).unwrap())
    }

    pub fn load_each_segment(
        &self,
        base: VirtAddr,
        paddr: &mut PhysAddr,
        header: Stage2LaunchInfo,
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
    ) -> (r: (Option<VirtAddr>, VirtAddr))
        requires
            self.wf(),
            header.wf(),
            old(paddr).wf(),
            old(ctx_perm).wf(),
            forall|i: int|
                0 <= i < self.load_segment_num_spec(base) ==> (
                #[trigger] self.load_segments()[i]).wf(),
        ensures
            old(ctx_perm) == ctx_perm,  // FIX IT LATER.
    {
        let mut load_virt_start = None::<VirtAddr>;
        let mut load_virt_end = VirtAddr::from(0u64);

        let mut i = 0usize;
        let segment_len = self.load_segment_num(base);
        while i < segment_len
            invariant
                self.wf(),
                header.wf(),
                ctx_perm.wf(),
                forall|i: int|
                    0 <= i < self.load_segment_num_spec(base) ==> (
                    #[trigger] self.load_segments()[i]).wf(),
                i <= segment_len,
                segment_len == self.load_segment_num_spec(base),
            decreases segment_len - i,
        {
            log_str!("Loading ELF segment ");
            log_int!(i);
            log_str_ln!("...");

            let (updated_phys_addr, vaddr_start, vaddr_end) = #[verus_spec(with Tracked(ctx_perm))]
            load_elf_segment(self.get_segment(i, base), *paddr, header);

            // Remember the mapping range's lower and upper bounds to pass it on
            // the kernel later. Note that the segments are being iterated over
            // here in increasing load order.
            if load_virt_start.is_none() {
                load_virt_start = Some(vaddr_start);
            }
            load_virt_end = vaddr_end;
            // Advance the physical address pointer for the next segment.
            assume(updated_phys_addr@ + (vaddr_end@ - vaddr_start@) < u64::MAX); // FIX IT LATER.
            *paddr = PhysAddr::from(updated_phys_addr.0 + (vaddr_end.0 - vaddr_start.0));
            i += 1;

            assume(ctx_perm.wf());  // FIX IT LATER.
        }

        assume(ctx_perm == old(ctx_perm));  // FIX IT LATER.

        (load_virt_start, load_virt_end)
    }
}

impl<'a> ElfLoadSegement<'a> {
    pub uninterp spec fn vaddr_begin(self) -> VirtAddr;

    pub uninterp spec fn vaddr_end(self) -> VirtAddr;

    #[verifier::external_body]
    pub fn vaddr_range(&self) -> (r: Range<VirtAddr>)
        requires
            self.wf(),
        ensures
            r.start == self.vaddr_begin(),
            r.end == self.vaddr_end(),
    {
        let begin = VirtAddr(self.0.vaddr_range.vaddr_begin as u64);
        let end = VirtAddr(self.0.vaddr_range.vaddr_end as u64);
        Range { start: begin, end }
    }
}

} // verus!
