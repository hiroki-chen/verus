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
//! - [`ElfLoadSegment`]: A wrapper for individual ELF load segments with address validation
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

use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::paging::PageTablePath;
use crate::{kdebug, kinfo, Stage2LaunchInfo};

verus! {

#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
        Ghost(segment_index): Ghost<usize>
    requires
        old(ctx_perm).wf_with(ctx),
        segment.wf(),
        old(paddr).wf(),
        old(paddr)@ % PAGE_SIZE == 0,
        header.wf_for_loading(old(ctx_perm).pgtable_perm.mapping_space),
        header.get_elf() matches Some(elf_file) && segment == elf_file.load_segments()[segment_index as int],
        segment.wf_with_load_base(*old(paddr)),
    ensures
        final(paddr)@ == old(paddr)@ + (r.end@ - r.start@),
        final(paddr)@ % PAGE_SIZE == 0,
        r.wf(),
        r.start@ == segment.vaddr_begin()@,
        r.end@ == segment.vaddr_end().page_align_up_spec()@,
        r.start@ % PAGE_SIZE == 0,
        r.end@ % PAGE_SIZE == 0,
        final(ctx_perm).pgtable_perm.mapping_space == old(ctx_perm).pgtable_perm.mapping_space,
        /* Non overflowing properties... */
)]
fn load_elf_segment(
    ctx: DekoPPtr<DekoCpuCtx>,
    segment: ElfLoadSegment,
    paddr: &mut PhysAddr,
    header: Stage2LaunchInfo,
) -> (r: VaddrRange) {
    // Find the segment's bounds
    // All ELF segments should be aligned to the page size. If not, there's
    // the risk of pvalidating a page twice, bail out if so. Note that the
    // ELF reading code had already verified that the individual segments,
    // with bounds specified as in the ELF file, are non-overlapping.
    let segment_start = segment.vaddr_range().start;
    let segment_end = segment.vaddr_range().end.page_align_up();
    let segment_len = segment_end.0 - segment_start.0;

    kinfo!("Mapping ELF segment", segment.vaddr_range(), "to", paddr, "with length", segment_len=>hex);

    // Although we've checked in the spec that the segment start is page-aligned,
    // double-check here to avoid any risk just to ensure safety.
    if core::intrinsics::unlikely(segment_start.0 % PAGE_SIZE != 0) {
        proof {
            assert(false);
        }

        crate::die("ELF segment virtual address not page-aligned!");
    }

    #[verus_spec(with Tracked(ctx_perm))]
    crate::mm::paging::map_and_validate(ctx, header, segment_start, segment_end, *paddr);

    unsafe { #[verus_spec(with Tracked(ctx_perm))] segment.copy_file_contents(); }
    proof {
        assert(segment_len % PAGE_SIZE == 0);
        assert(paddr@ % PAGE_SIZE == 0);
        vstd::arithmetic::div_mod::lemma_mod_adds(
            paddr@ as int,
            segment_len as int,
            PAGE_SIZE as int,
        );
    }

    *paddr = PhysAddr(paddr.0 + segment_len);
    segment_start..segment_end
}

/// A thin wrapper around [`elf::Elf64File`] to be used in Verus code.
///
/// Note that for the time being we do not intend to verify any functionality
/// related to ELF parsing. Thus, this struct only serves as a marker type
/// to allow us to pass ELF files around in Verus code.
#[verifier::external_body]
pub struct ElfFile<'a>(elf::Elf64File<'a>);

#[verifier::external_body]
pub struct ElfLoadSegment<'a>(Elf64ImageLoadSegment<'a>);

impl<'a> WellFormed for ElfFile<'a> {
    open spec fn wf(&self) -> bool {
        let segments = self.load_segments();

        &&& forall|i: int|
            #![trigger segments[i]]
            0 <= i < segments.len()
                ==> segments[i].wf()
        // Ensure that the segments are non-overlapping in virtual address space and ordered.
        &&& forall|i: int|
            #![trigger segments[i]]
            1 <= i < segments.len() ==> segments[i - 1].vaddr_end()@ <= segments[i].vaddr_begin()@
    }
}

impl<'a> WellFormed for ElfLoadSegment<'a> {
    open spec fn wf(&self) -> bool {
        // The build system should ensure that the segment
        // virtual address range is at higher half.
        &&& self.vaddr_end()@ > self.vaddr_begin()@ >= VADDR_UPPER_MASK
        &&& self.vaddr_end()@ + PAGE_SIZE - 1 < u64::MAX
        &&& self.vaddr_begin()@ % PAGE_SIZE == 0  // begin is aligned.
        &&& PageTablePath::from_vaddr(self.vaddr_begin()).is_normalized()
            && PageTablePath::from_vaddr(self.vaddr_end()).is_normalized()
    }
}

impl<'a> ElfFile<'a> {
    pub uninterp spec fn get_vaddr_alloc_base_spec(&self) -> VirtAddr;

    pub uninterp spec fn new_spec(start: u64, end: u64) -> Option<Self>;

    pub uninterp spec fn load_segments(&self) -> Seq<ElfLoadSegment>;

    pub uninterp spec fn entry_point(&self, base: VirtAddr) -> VirtAddr;

    pub open spec fn paddr_after_load_ith_segment(&self, i: usize, base: PhysAddr) -> PhysAddr
        recommends
            self.wf(),
            base.wf(),
            i < self.load_segments().len() as usize,
    {
        let lengths = self.load_segments().subrange(0, i + 1).map_values(
            |seg: ElfLoadSegment|
                (seg.vaddr_end().page_align_up_spec()@ - seg.vaddr_begin()@) as usize,
        );
        let length_so_far = lengths.fold_right(
            |acc: usize, len: usize| (acc + len) as usize,
            0usize,
        );
        PhysAddr((base@ + length_so_far) as u64)
    }

    /// Validates that the entire ELF file is constrainetd.
    ///
    /// This only requires that the last segment is constrained
    /// because we ensure that the segments are non-overlapping
    /// and ordered in the [`ElfFile::wf`] spec function.
    #[verifier::inline]
    pub open spec fn wf_with_load_base(&self, load_base: PhysAddr) -> bool
        recommends
            load_base.wf(),
            self.wf(),
    {
        self.load_segments().last().wf_with_load_base(load_base)
    }

    #[verifier::inline]
    pub open spec fn wf_with_ms(&self, load_base: PhysAddr, ms: MappingSpace) -> bool
        recommends
            ms.wf(),
            self.wf(),
    {
        &&& self.load_segments().first().wf_with_ms(load_base, ms)
        &&& self.load_segments().last().wf_with_ms(load_base, ms)
    }

    #[verifier::inline]
    pub open spec fn segment_in_loaded_range_spec(
        &self,
        segment: ElfLoadSegment,
        base: VirtAddr,
    ) -> bool {
        self.load_segments().contains(segment)
    }

    pub proof fn lemma_last_wf_with_load_base_implies_all(&self, load_base: PhysAddr)
        requires
            self.wf(),
            load_base.wf(),
            self.wf_with_load_base(load_base),
        ensures
            forall|i: int|
                #![trigger self.load_segments()[i]]
                0 <= i < self.load_segments().len() ==> {
                    let now_paddr = self.paddr_after_load_ith_segment(i as usize, load_base);

                    self.load_segments()[i].wf_with_load_base(now_paddr)
                },
    {
        admit()
    }

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
            r.wf(),
            r == Self::new_spec(start_paddr@, end_paddr@),
    {
        let bytes = unsafe {
            core::slice::from_raw_parts(
                start_paddr.0 as *const u8,
                (end_paddr.0 - start_paddr.0) as usize,
            )
        };

        Some(Self(elf::Elf64File::read(bytes).ok()?))
    }

    #[verifier::external_body]
    pub fn read(bytes: &'a [u8]) -> (r: Option<Self>)
        ensures
            r.wf(),
    {
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
            r.wf(),
            r@ >= VADDR_UPPER_MASK,
    {
        self.0.image_load_vaddr_alloc_info().range.vaddr_begin.into()
    }

    #[inline]
    #[verifier::external_body]
    pub fn load_segment_num(&self, base: VirtAddr) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.load_segments().len() as usize,
    {
        self.0.image_load_segment_iter(base.0).count()
    }

    #[verifier::external_body]
    pub fn get_segment(&self, index: usize, base: VirtAddr) -> (r: ElfLoadSegment)
        requires
            self.wf(),
            index < self.load_segments().len() as usize,
        ensures
            r == self.load_segments()[index as int],
    {
        ElfLoadSegment(self.0.image_load_segment_iter(base.0).nth(index).unwrap())
    }

    #[verifier::spinoff_prover]
    pub fn load_each_segment(
        &self,
        ctx: DekoPPtr<DekoCpuCtx>,
        base: VirtAddr,
        paddr: &mut PhysAddr,
        header: Stage2LaunchInfo,
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
    ) -> (r: (Option<VirtAddr>, VirtAddr))
        requires
            self.wf(),
            header.get_elf() matches Some(elf_file) && elf_file == *self,
            header.wf_for_loading(old(ctx_perm).pgtable_perm.mapping_space),
            header.get_igvm_param_block_spec().find_kernel_region_spec() matches Some((kstart, _))
                && kstart == *old(paddr),
            old(paddr).wf(),
            old(ctx_perm).wf_with(ctx),
            old(paddr)@ % PAGE_SIZE == 0,
            base@ >= VADDR_LOWER_MASK,
        ensures
            final(ctx_perm).wf_with(ctx),
            final(ctx_perm).pgtable_perm.mapping_space == old(ctx_perm).pgtable_perm.mapping_space,
            r matches (Some(vaddr_start), vaddr_end) ==> {
                &&& vaddr_start.wf()
                &&& vaddr_end.wf()
                &&& vaddr_start@ % PAGE_SIZE == 0
                &&& vaddr_end@ % PAGE_SIZE == 0
                &&& base@ < vaddr_start@ < vaddr_end@ < u64::MAX
                &&& final(paddr)@ > old(paddr)@
            },
            final(paddr)@ % PAGE_SIZE == 0,
    {
        let mut load_virt_start = None::<VirtAddr>;
        let mut load_virt_end = VirtAddr::from(0u64);

        let mut i = 0usize;
        let segment_len = self.load_segment_num(base);
        while i < segment_len
            invariant
                i <= segment_len,
                i == 0 ==> {
                    load_virt_start matches None && load_virt_end@ == 0
                },
                0 < i ==>
                {
                    &&& paddr@ == self.paddr_after_load_ith_segment(i, *old(paddr))@
                    &&& load_virt_start matches Some(vaddr)
                    && vaddr.wf()
                    && vaddr@ % PAGE_SIZE == 0
                    && load_virt_end.wf()
                    && load_virt_end@ % PAGE_SIZE == 0
                    && base@ < vaddr@ < load_virt_end@ < u64::MAX
                },
                segment_len == self.load_segments().len() as usize,
                header.get_elf() matches Some(elf_file) && elf_file == *self,
                header.wf_for_loading(ctx_perm.pgtable_perm.mapping_space),
                header.get_igvm_param_block_spec().find_kernel_region_spec() matches Some((kstart, _)) && kstart == *old(paddr),
                self.wf(),
                paddr.wf(),
                paddr@ % PAGE_SIZE == 0,
                ctx_perm.wf_with(ctx),
                ctx_perm.pgtable_perm.mapping_space == old(ctx_perm).pgtable_perm.mapping_space,
                PAGE_SIZE == 0x1000,
            decreases segment_len - i,
        {
            kinfo!("Loading ELF segment @[", i, "]...");

            let segment = self.get_segment(i, base);

            proof {
                assert(segment.wf_with_load_base(*paddr)) by {
                    assert(self.wf());
                    assert(self.wf_with_load_base(*old(paddr)));
                    assert(paddr.wf());
                    // The proof is tricky because old states and new states are mixed
                    // here and verus has trouble dealing with old(xx) inside loop bodies
                    // be extra careful.

                    // assert(paddr@ == self.paddr_after_load_ith_segment(i, old_paddr)@);
                    // self.lemma_last_wf_with_load_base_implies_all(old_paddr);

                    admit();
                }
            }

            // We are having trouble with verifying the following call.
            let range =
                #[verus_spec(with Tracked(ctx_perm), Ghost(i))]
            load_elf_segment(ctx, segment, paddr, header);
            let vaddr_start = range.start;
            let vaddr_end = range.end;

            // Remember the mapping range's lower and upper bounds to pass it on
            // the kernel later. Note that the segments are being iterated over
            // here in increasing load order.
            if load_virt_start.is_none() {
                load_virt_start = Some(vaddr_start);
            }
            load_virt_end = vaddr_end;
            i += 1;

            proof {
                assume(ctx_perm.wf_with(ctx));  // FIX IT LATER.
                assume(paddr@ % PAGE_SIZE == 0);
                assume(paddr.wf());
                assume(paddr@ == self.paddr_after_load_ith_segment(i, *old(paddr))@);
                // Let's revisit the base later; might need to add something for segment.
                assume(load_virt_start matches Some(vaddr) && base@ < vaddr@ < load_virt_end@ < u64::MAX);
            }
        }

        proof {
            if i == 0 {
                assert(load_virt_start.is_none());
                assert(load_virt_end@ == 0);
            } else {
                assume(paddr@ > old(paddr)@);  // FIX IT LATER.
                assert(load_virt_start matches Some(vaddr) && vaddr.wf() && load_virt_end.wf()
                    && vaddr@ % PAGE_SIZE == 0 && load_virt_end@ % PAGE_SIZE == 0 && base@ < vaddr@ < load_virt_end@ < u64::MAX);
            }

            assume(*ctx_perm == *old(ctx_perm));  // FIX IT LATER.

        }

        (load_virt_start, load_virt_end)
    }

    #[inline]
    #[verifier::external_body]
    pub fn get_entry_point(&self, base: VirtAddr) -> (r: VirtAddr)
        requires
            self.wf(),
            base.wf(),
        ensures
            r == self.entry_point(base),
            r.wf(),
            r@ % PAGE_SIZE == 0,
    {
        VirtAddr::from(self.0.get_entry(base.0) as u64)
    }
}

#[verus_verify]
impl<'a> ElfLoadSegment<'a> {
    pub uninterp spec fn vaddr_begin(self) -> VirtAddr;

    pub uninterp spec fn vaddr_end(self) -> VirtAddr;

    pub uninterp spec fn file_contents_len_spec(self) -> usize;

    pub uninterp spec fn exec_spec(self) -> bool;

    pub uninterp spec fn write_spec(self) -> bool;

    /// Returns the length of this ELF load segment in bytes.
    #[verifier::inline]
    pub open spec fn segment_len(self) -> usize {
        (self.vaddr_end()@ - self.vaddr_begin()@) as usize
    }

    /// Validates that this ELF load segment is well-formed when loaded at a specific physical base address.
    ///
    /// This specification function performs overflow and bounds checking to ensure that loading
    /// the segment at the given physical base address will not cause arithmetic overflow or
    /// exceed safe address space limits.
    ///
    /// # Parameters
    ///
    /// * `load_base` - The physical address where the segment will be loaded. Must be well-formed.
    ///
    /// # Returns
    ///
    /// `true` if the segment can be safely loaded at the specified base address, `false` otherwise.
    ///
    /// # Safety Requirements
    ///
    /// This function verifies that:
    /// - The total physical address range (base + segment size) remains below the safe upper limit
    /// - No arithmetic overflow occurs when computing the final physical address
    /// - The segment respects the 64-bit address space constraints (below `0x000f_ffff_ffff_f000`)
    ///
    /// # Usage
    ///
    /// This function is typically called during ELF loading to verify that segments can be
    /// safely placed at their intended physical addresses without violating memory safety.
    ///
    /// ```rust,ignore
    /// if segment.wf_with_load_base(phys_base) {
    ///     // Safe to proceed with loading
    /// } else {
    ///     // Loading would cause overflow or exceed limits
    /// }
    /// ```
    #[verifier::inline]
    pub open spec fn wf_with_load_base(self, load_base: PhysAddr) -> bool
        recommends
            load_base.wf(),
    {
        let vaddr_begin = self.vaddr_begin();
        let vaddr_end = self.vaddr_end();

        load_base@ + (vaddr_end.page_align_up_spec()@ - vaddr_begin@) < 0x000f_ffff_ffff_f000
    }

    /// Validates that this ELF load segment fits within the specified mapping space when loaded.
    ///
    /// This specification function ensures that both the start and end addresses of the segment,
    /// when loaded at the given physical base address, fall within the valid range of the
    /// kernel's address space as defined by the mapping space.
    ///
    /// # Parameters
    ///
    /// * `load_base` - The physical address where the segment will be loaded
    /// * `ms` - The mapping space that defines valid address ranges. Must be well-formed.
    ///
    /// # Returns
    ///
    /// `true` if the entire segment (from start to page-aligned end) fits within the kernel's
    /// address space range, `false` otherwise.
    ///
    /// # Address Range Validation
    ///
    /// This function computes the physical address range that the segment will occupy:
    /// - Start address: `load_base + segment.vaddr_begin()`
    /// - End address: `load_base + segment.vaddr_end().page_align_up()`
    ///
    /// Both addresses must be within the kernel's valid address range as specified by
    /// `ms.kernel.in_range_spec()`.
    ///
    /// # Usage
    ///
    /// This function is used during ELF loading to ensure segments don't extend beyond
    /// the allocated kernel address space:
    ///
    /// ```rust,ignore
    /// if segment.wf_with_ms(phys_base, mapping_space) {
    ///     // Segment fits within kernel address space
    /// } else {
    ///     // Segment would exceed kernel boundaries
    /// }
    /// ```
    ///
    /// # Note
    ///
    /// The end address is page-aligned up to ensure proper page boundary handling,
    /// and the validation checks `end - 1` to account for inclusive range semantics.
    pub open spec fn wf_with_ms(self, load_base: PhysAddr, ms: MappingSpace) -> bool
        recommends
            ms.wf(),
    {
        let vaddr_begin = self.vaddr_begin();
        let vaddr_end = self.vaddr_end();

        let start = load_base@ + vaddr_begin@;
        let end = load_base@ + vaddr_end.page_align_up_spec()@;

        ms.kernel.in_range_spec(PhysAddr(start as u64)) && ms.kernel.in_range_spec(
            PhysAddr((end - 1) as u64),
        )
    }

    #[inline]
    #[verifier::external_body]
    pub fn exec(&self) -> bool
        requires
            self.wf(),
        returns
            self.exec_spec(),
    {
        self.0.flags.contains(elf::Elf64PhdrFlags::EXECUTE)
    }

    #[inline]
    #[verifier::external_body]
    pub fn write(&self) -> bool
        requires
            self.wf(),
        returns
            self.write_spec(),
    {
        self.0.flags.contains(elf::Elf64PhdrFlags::WRITE)
    }

    #[verifier::external_body]
    pub fn vaddr_range(&self) -> (r: Range<VirtAddr>)
        requires
            self.wf(),
        ensures
            r.start == self.vaddr_begin(),
            r.end == self.vaddr_end(),
            r.start@ % PAGE_SIZE == 0,
            r.start@ < r.end@ < u64::MAX,
            r.end.page_align_up_spec()@ - r.start@ < u32::MAX,
    {
        let begin = VirtAddr(self.0.vaddr_range.vaddr_begin as u64);
        let end = VirtAddr(self.0.vaddr_range.vaddr_end as u64);
        Range { start: begin, end }
    }

    /// Copies the contents of this ELF load segment from its source location
    /// in physical memory to its destination virtual address.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the destination virtual address is valid
    /// and mapped to physical memory that can be written to.
    #[verus_spec(r =>
        with
            Tracked(ctx_perm): Tracked<&DekoCpuCtxPermission>
    )]
    #[verifier::external_body]
    pub unsafe fn copy_file_contents(&self)
        requires
            self.wf(),
            ctx_perm.wf(),
            ctx_perm.pgtable_perm.mapped_region(
                self.vaddr_begin()..self.vaddr_end().page_align_up_spec(),
            ),
        ensures
            true,
    {
        let end = VirtAddr(self.0.vaddr_range.vaddr_end).page_align_up();
        kinfo!("Copying ELF segment file contents to [",
                self.0.vaddr_range.vaddr_begin => hex, " - ",
                end.0 => hex, "]");

        let mut buf = core::slice::from_raw_parts_mut(
            self.0.vaddr_range.vaddr_begin as *mut u8,
            (end.0 - self.0.vaddr_range.vaddr_begin) as usize,
        );

        kdebug!("buf:", &buf[..64]);

        let file_contents = self.0.file_contents;
        buf[..file_contents.len()].copy_from_slice(file_contents);
        // Pad zeros.
        buf[file_contents.len()..].fill(0);

        kinfo!("Finished copying ELF segment file contents.");
    }
}

} // verus!
