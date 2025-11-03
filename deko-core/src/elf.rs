use deko_std::prelude::*;
use elf::Elf64ImageLoadSegment;
use vstd::bytes;
use vstd::prelude::*;

use crate::{log_hex_dump, log_hex_prefixed, log_int, log_str, log_str_ln};

verus! {

/// A thin wrapper around `xmas_elf::ElfFile` to be used in Verus code.
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
        true
    }
}

impl<'a> ElfFile<'a> {
    pub uninterp spec fn load_segment_num_spec(&self, base: VirtAddr) -> usize;

    pub uninterp spec fn get_vaddr_alloc_base_spec(&self) -> VirtAddr;

    pub uninterp spec fn segment_in_loaded_range_spec(
        &self,
        segment: ElfLoadSegement,
        base: VirtAddr,
    ) -> bool;

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
    pub fn load_each_segment(
        &self,
        base: VirtAddr,
        paddr: &mut PhysAddr,
        header: Stage2LaunchInfo,
        f: impl Fn(ElfLoadSegement, PhysAddr, Stage2LaunchInfo) -> (PhysAddr, VirtAddr, VirtAddr),
    ) -> (r: (Option<VirtAddr>, VirtAddr))
        requires
            self.wf(),
            old(paddr).wf(),
            header.wf(),
    // forall|segment: ElfLoadSegement|
    //     self.segment_in_loaded_range_spec(segment, base) ==> f.requires(
    //         (segment, paddr, header),
    //     ), <- needs to add something about the updated paddr

    {
        let mut load_virt_start = None::<VirtAddr>;
        let mut load_virt_end = VirtAddr::from(0u64);

        for (i, segment) in self.0.image_load_segment_iter(base.0).enumerate() {
            log_str!("Loading ELF segment ");
            log_int!(i);
            log_str_ln!("...");

            let (updated_phys_addr, vaddr_start, vaddr_end) = f(
                ElfLoadSegement(segment),
                *paddr,
                header,
            );
            // Remember the mapping range's lower and upper bounds to pass it on
            // the kernel later. Note that the segments are being iterated over
            // here in increasing load order.
            if load_virt_start.is_none() {
                load_virt_start = Some(vaddr_start);
            }
            load_virt_end = vaddr_end;

            // Advance the physical address pointer for the next segment.
            *paddr = PhysAddr::from(updated_phys_addr.0 + vaddr_end.0 - vaddr_start.0);
        }

        (load_virt_start, load_virt_end)
    }
}

} // verus!
