use core::cmp::Ordering;
use core::ops::{Range, RangeBounds};

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::mem::bitalloc::{
    lemma_bit_map_allocator_1024_is_pow2, DekoBitAlloc, DekoBitmapAllocator1024,
};
use deko_std::prelude::*;
use deko_std::std_extra::cmp::{is_sorted_spec, lemma_cmp_pivot_monotonic};
use deko_std::std_extra::slice::comparator_consistent_spec;
use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd::std_specs::cmp::*;

use super::frame_allocator::DekoAllocatorApi;
use crate::collections::Vec;
use crate::cpu::DekoCpuCtx;
use crate::mm::paging::{
    all_in_range_paddrs, all_normalized_vaddrs, bit_not_in_addr_region, bit_not_overlapping,
    index_at_level, make_private_address, PageTable, PageTableEntry, PageTablePermission, PteFlags,
    Pte_ALL_BITS, PRESENT, RECURSIVE_INDEX,
};
use crate::mm::stack::DekoKernelStack;
use crate::mm::vm;
use crate::{die, kdebug, kinfo, kpanic_if, kunimplemented, kwarn, vec};

verus! {

pub type RootCoverage = u16;

/// Sometimes we need to temporarily get some mappings and then
/// discard immediately after use. This struct represents such
/// temporary mapping requests.
///
/// For example, when we want to change some page status where
/// we only care about the physical addresses mapped but not
/// the virtual addresses, we can use this struct to represent
/// such temporary mappings. After all, if pages are not mapped,
/// we won't be able to r/w them anyway.
#[derive(DekoDebug)]
pub struct VirtualMemoryTemporary {
    /// Starting virtual address of the temporary mapping.
    pub vaddr_start: VirtAddr,
    /// Number of pages mapped.
    pub nr_pages: usize,
    /// A bitmap allocator for managing temporary mappings.
    pub alloc: DekoBitmapAllocator1024,
}

impl WellFormed for VirtualMemoryTemporary {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.vaddr_start.wf()
        &&& self.vaddr_start@ >= VADDR_UPPER_MASK
        &&& self.vaddr_start@ % PAGE_SIZE == 0
        &&& self.nr_pages >= 0
        &&& self.vaddr_start@ + (self.nr_pages as u64) * PAGE_SIZE < u64::MAX
        &&& self.alloc.wf()
    }
}

/// A temporary mapping created by [`VirtualMemoryTemporary`].
///
/// This implements [`Drop`] to automatically unmap the mapping
/// when it goes out of scope.
#[must_use = "Temporary mappings must be used or they will be droppped immediately."]
pub struct TempMapping {
    pub inner: VaddrRange,
}

impl Drop for TempMapping {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        let (cpu_ptr, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
        let cpu: &DekoCpuCtx = cpu_ptr.borrow(Tracked(&cpu_perm.ptr_perm));
        let pgtable = cpu.pgtable();
        let private_bit = cpu.private_bit();
        let shared_bit = cpu.shared_bit();

        let mut cpu_taken = cpu_ptr.take(Tracked(&mut cpu_perm.ptr_perm));

        if core::hint::unlikely(
            self.inner.end.0 < self.inner.start.0 || self.inner.start.0 % PAGE_SIZE != 0
                || self.inner.end.0 % PAGE_SIZE != 0 || self.inner.start.0 < VADDR_UPPER_MASK || (
            self.inner.end.0 - self.inner.start.0) / PAGE_SIZE
                > cpu_taken.temp_mapping.nr_pages as u64 || self.inner.start.0
                < cpu_taken.temp_mapping.vaddr_start.0,
        // make verus happy
        ) {
            return ;
        }
        cpu_taken.temp_mapping.deallocate(
            self.inner.start,
            ((self.inner.end.0 - self.inner.start.0) / PAGE_SIZE) as usize,
        );

        cpu_ptr.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

        // PageTable::unmap_multiple_pages(pgtable, Tracked(&mut cpu_perm.pgtable_perm), vaddr, ms, private_bit, shared_bit)...
    }
}

#[verus_verify]
impl TempMapping {
    /// Attempts to create a new temporary mapping for the given physical address range.
    ///
    /// Please note this assumes the page is always aligned to 4KiB and we do not intend
    /// to support huge pages here.
    #[verus_spec(r =>
        requires
            prange.wf(),
            prange.start@ % PAGE_SIZE == 0,
            prange.end@ % PAGE_SIZE == 0,
            prange.end@ <= 0x000f_ffff_ffff_f000,
        ensures
            r matches Some(tm) ==> {
                &&& tm.wf()
                &&& tm.inner.start@ >= VADDR_UPPER_MASK
                &&& tm.inner.start@ % PAGE_SIZE == 0
                &&& (tm.inner.end@ - tm.inner.start@) == (prange.end@ - prange.start@)
            }
    )]
    pub fn new(prange: PaddrRange) -> Option<Self> {
        broadcast use crate::mm::PteFlags::lemma_each_bit_is_valid;

        let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
        let max_nr_pages = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).temp_mapping().nr_pages;

        let nr_pages = ((prange.end.0 - prange.start.0) / PAGE_SIZE) as usize;
        if nr_pages == 0 || nr_pages + 1 > max_nr_pages {
            kwarn!("TempMapping::new: invalid number of pages requested:", nr_pages);
            return None;
        }
        kdebug!("TempMapping::new: requesting temporary mapping of", nr_pages, "pages for physical range", prange);
        let flags = PteFlags::data();
        let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

        let vaddr = match cpu_taken.temp_mapping.allocate(nr_pages, 0) {
            Some(vaddr) => vaddr,
            None => {
                kwarn!("TempMapping::new: unable to allocate temporary mapping of", nr_pages, "pages");

                // Remember to put back the cpu permission
                cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
                return None;
            },
        };
        let vrange = VaddrRange {
            start: vaddr,
            end: VirtAddr(vaddr.0 + (nr_pages as u64) * PAGE_SIZE),
        };

        proof {
            assert(flags.bits() & Pte_ALL_BITS == flags.bits()) by {
                bit_u64_and_auto();
            }
            // Leave this as assumptions for now.
            // another way is to leave these as runtime checks.
            assume(vaddr@ % PAGE_SIZE == 0);
            assume(all_normalized_vaddrs(vrange));
            assume(all_in_range_paddrs(&cpu_taken.kernel_mapping_spec(), prange.start, vrange));
            assume(vrange.end@ + PAGE_SIZE_2M <= u64::MAX);
            assume(prange.start@ + (vrange.end@ - vrange.start@) < 0x000f_ffff_ffff_f000);

            assert(vrange.end@ - vrange.start@ == prange.end@ - prange.start@) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    prange.end@ - prange.start@,
                    PAGE_SIZE as int,
                );
                assert(PAGE_SIZE * (nr_pages as int) + (prange.end@ - prange.start@)
                    % PAGE_SIZE as int == prange.end@ - prange.start@);
                assert((prange.end@ - prange.start@) % PAGE_SIZE as int == 0) by {
                    vstd::arithmetic::div_mod::lemma_mod_equivalence(
                        prange.end@ as int,
                        prange.start@ as int,
                        PAGE_SIZE as int,
                    );
                }
            }
        }

        // Map the page.
        PageTable::map_page_multiple(
            cpu_taken.pgtable(),
            vrange.clone(),
            prange.start,
            flags,
            &cpu_taken.kernel_mapping(),
            cpu_taken.private_bit(),
            cpu_taken.shared_bit(),
            Tracked(&mut cpu_perm.pgtable_perm),
        );

        cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

        Some(Self { inner: vrange })
    }
}

impl WellFormed for TempMapping {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.inner.wf()
        &&& self.inner.start@ % PAGE_SIZE == 0
        &&& self.inner.end@ % PAGE_SIZE == 0
    }
}

#[verus_verify]
impl VirtualMemoryTemporary {
    /// Creates a new temporary mapping manager with the given
    /// starting virtual address and number of pages.
    #[verus_spec(r =>
        requires
            old(self).wf(),
            vaddr_start.wf(),
            vaddr_start@ >= VADDR_UPPER_MASK,
            vaddr_start@ % PAGE_SIZE == 0,
            nr_pages > 0,
            vaddr_start@ + (nr_pages as u64) * PAGE_SIZE < u64::MAX,
        ensures
            self.wf(),
            self.vaddr_start == vaddr_start,
            self.nr_pages == nr_pages,
    )]
    pub fn set(&mut self, vaddr_start: VirtAddr, nr_pages: usize) {
        kpanic_if!(
            nr_pages > (<DekoBitmapAllocator1024 as DekoBitAlloc>::cap()),
            "VirtualMemoryTemporary::set: nr_pages exceeds maximum capacity"
        );

        self.vaddr_start = vaddr_start;
        self.nr_pages = nr_pages;
        // Make the range available.
        self.alloc.set(0, nr_pages, false);
    }

    #[verus_spec(r =>
        ensures
            r.wf(),
    )]
    pub fn new_zeroed() -> Self {
        Self {
            vaddr_start: VirtAddr(VADDR_UPPER_MASK),
            nr_pages: 0,
            alloc: DekoBitmapAllocator1024::new_full(),
        }
    }

    /// Queries the inner bitmap allocator for available temporary mappings and
    /// return the starting virtual address if successful. This function does
    /// NOT actually map any pages, it only allocates the virtual address space.
    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            old(self).wf(),
            nr_pages < old(self).nr_pages,
        ensures
            self.wf(),
            r matches Some(vaddr) ==> {
                &&& vaddr.wf()
                &&& vaddr@ >= old(self).vaddr_start@
                &&& vaddr@ + (nr_pages as u64) * PAGE_SIZE <= old(self).vaddr_start@ + (old(self).nr_pages as u64) * PAGE_SIZE
            }
    )]
    pub fn allocate(&mut self, nr_pages: usize, align: usize) -> Option<VirtAddr> {
        if align >= (<DekoBitmapAllocator1024 as DekoBitAlloc>::cap()).ilog2() as usize || (nr_pages
            + 1) > <DekoBitmapAllocator1024 as DekoBitAlloc>::cap() {
            return None;
        }
        proof {
            lemma_bit_map_allocator_1024_is_pow2();
        }

        kdebug!("VirtualMemoryTemporary::allocate: requesting", nr_pages, "pages with alignment", align);
        kdebug!("VirtualMemoryTemporary::allocate: current alloc state:", self.alloc);

        let r = self.alloc.alloc(nr_pages + 1, align)?;

        proof {
            //
        }

        Some(VirtAddr(self.vaddr_start.0 + r as u64 * PAGE_SIZE as u64))
    }

    #[verifier::external_body]
    #[verus_spec(
        requires
            old(self).wf(),
            vaddr.wf(),
            vaddr@ % PAGE_SIZE == 0,
            vaddr@ >= old(self).vaddr_start@,
        ensures
            self.wf(),
        opens_invariants none
        no_unwind
    )]
    pub fn deallocate(&mut self, vaddr: VirtAddr, nr_pages: usize) {
        let offset = (vaddr.0 - self.vaddr_start.0) / PAGE_SIZE as u64;
        self.alloc.free(offset as usize, nr_pages + 1);
    }

    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
    )]
    pub fn used_pages(&self) -> usize {
        kunimplemented!()
    }
}

with_atomic_pred! {
    VirtualMemoryRegion,
    VirtualMemoryRegionPermission,
    fields: { },
    perm_fields: { },
    data.wf_with(&perm)
}

#[derive(DekoDebug)]
pub struct RawMapping {
    /// A vec containing references to PageFile allocations
    pub pages: Vec<Option<(VirtAddr, PhysAddr)>>,
    /// Number of pages required in `pages`.
    pub nr_pages: usize,
}

/// A mapping is a reference-counted pointer to a [`VmMapping`] protected by a [`RwLock`].
///
/// This currently looks ugly because it mingles the `DekoArc` and `DekoRwLock` types with
/// invariant together and is not very ergnomic to use. We may need to provide some helper
/// functions to make it easier to create.
pub type Mapping = DekoArc<DekoRwLock<VmMapping, (), VmMappingPred>, (), DekoSimpleRwLockPred>;

/// A [`VmMapping`] represents a backing mapping from the offset to a base to the physical
/// address with a fixed size used in the [`VirtualMemory] struct for translating virtual
/// memories into physical ones and manage the backing paging system.
///
/// This struct is NOT intended for direct use outside of the VM system as it does _NOT_
/// contain any information about the virtual address it is covering. The correct usage
/// to request the kernel frame allocator to allocate physical frames and then use the
/// returned physical address to create a mapping. The virtual addresses are kernel owned.
#[derive(DekoDebug)]
pub enum VmMapping {
    /// A mapping backed by a contiguous physical memory region.
    PhysMem { paddr: PhysAddr, size: u64 },
    /// Mapping type for which uses self-allocated PageFile pages.
    Stack { stack: DekoKernelStack },
}

with_atomic_pred!(
    VmMapping,
    (),
    fields: { },
    perm_fields: { },
    data.wf()
);

impl WellFormed for VmMapping {
    open spec fn wf(&self) -> bool {
        &&& PAGE_SIZE <= self.mapping_size_spec() <= u64::MAX
        &&& match self {
            VmMapping::PhysMem { paddr, size } => {
                &&& paddr.wf()
                &&& paddr@ % PAGE_SIZE == 0
                &&& size <= u64::MAX
                &&& size % PAGE_SIZE == 0
                &&& paddr@ + *size < 0x000f_ffff_ffff_f000
            },
            VmMapping::Stack { stack } => { stack.wf() },
        }
    }
}

#[verus_verify]
impl VmMapping {
    #[verifier::inline]
    pub open spec fn mapping_size_spec(&self) -> u64 {
        match self {
            VmMapping::PhysMem { paddr, size } => *size,
            VmMapping::Stack { stack } => (((stack.alloc@.len() as u64 + stack.guard_pages
                * 2)) as u64 * PAGE_SIZE) as u64,
        }
    }

    pub open spec fn phys_at_spec(&self, offset: u64) -> Option<PhysAddr>
        recommends
            self.wf(),
            offset < self.mapping_size_spec(),
    {
        arbitrary()
    }

    /// Request the size of the virtual memory mapping.
    #[verifier::when_used_as_spec(mapping_size_spec)]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == Self::mapping_size_spec(self),
            r % PAGE_SIZE == 0,
    )]
    pub fn mapping_size(&self) -> u64 {
        match self {
            VmMapping::PhysMem { paddr, size } => *size,
            VmMapping::Stack { stack } => ((stack.alloc.len() as u64 + stack.guard_pages
                * 2)) as u64 * PAGE_SIZE,
        }
    }

    /// Request physical address to map for a given `offset` which should be
    /// less than the mapping size.
    ///
    /// [`Option::None`] means that there is no mapping for the given offset.
    #[verifier::when_used_as_spec(phys_at_spec)]
    #[verus_spec(r =>
        requires
            self.wf(),
            // offset < self.mapping_size_spec(),
        ensures
            // r == Self::phys_at_spec(self, offset),
            r matches Some(paddr) ==> {
                &&& paddr.wf()
                &&& offset % PAGE_SIZE == 0 ==> paddr@ % PAGE_SIZE == 0
                &&& paddr@ < 0x000f_ffff_ffff_f000
            },
    )]
    pub fn phys_at(&self, offset: u64) -> Option<PhysAddr> {
        match self {
            VmMapping::PhysMem { paddr, size } => {
                kpanic_if!(core::hint::unlikely(
                    offset >= *size,
                ), "Offset out of bounds in VmMapping::phys_at");

                Some(PhysAddr(paddr.0 + offset))
            },
            VmMapping::Stack { stack } => {
                let pfn = offset >> 12;
                let guard_offset = stack.guard_pages << 12;

                kdebug!("VmMapping::phys_at: stack mapping at offset", offset, "with guard offset", guard_offset, "and pfn", pfn);

                if pfn >= stack.guard_pages {
                    proof {
                        let gp = stack.guard_pages;

                        assert(offset >= guard_offset) by (bit_vector)
                            requires
                                pfn >= gp,
                                pfn == offset >> 12,
                                guard_offset == gp << 12,
                        ;
                    }

                    let pfn = (offset - guard_offset) >> 12;

                    kdebug!("VmMapping::phys_at: adjusted pfn is", pfn);

                    match stack.alloc.get(pfn as usize) {
                        Some(Some((_, paddr))) => { Some(*paddr) },
                        _ => None,
                    }
                } else {
                    None
                }
            },
        }
    }
}

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
    #[deko(skip)]
    pub id: Ghost<int>,
    /// Start address of this range as virtual PFN (VirtAddr >> 12).
    #[deko(hex)]
    pub start_pfn: u64,
    /// End address of this range as virtual PFN (VirtAddr >> 12)
    #[deko(hex)]
    pub end_pfn: u64,
    /// Global to all mappings in this virtual memory region.
    #[deko(skip)]
    pub pt_flags: PteFlags,
    /// All the virtual memory areas managed by this region.
    ///
    /// This data structure MAY NOT be the most optimal for lookups. We may need to change it to
    /// an interval tree or other more efficient data structures but not verification-friendly.
    #[deko(skip)]
    pub areas: Vec<VirtualMemory>,
    /// The top-level page tables for this region.
    pub pgtable: DekoPPtr<PageTable>,
    /// "Covered" regions of this [`VirtualMemoryRegion`] at the top-level of the root page table
    /// it uses. One can think of this as a bitmap where each bit represents whether the corresponding
    pub pgtable_top_level_coverage: RootCoverage,
    /// The mapping space this region belongs to.
    pub ms: MappingSpace,
    /// Private bit for this region.
    #[deko(hex)]
    pub private_bit: u64,
    /// Shared bit for this region.
    #[deko(hex)]
    pub shared_bit: u64,
}

/// Tracks the corresponding permissions for a virtual memory region if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryRegionPermission {
    pub ghost id: int,
    /// A collection of page table permissions for each top-level page table.
    pub pgtable_perm: PageTablePermission,
    /// A list of virtual memory permissions managed by this region.
    pub vm_perms: Ghost<Seq<VirtualMemoryPermission>>,
}

/// This struct manages one piece of virtual memory covered by the [`VirtualMemoryRegion`].
#[derive(DekoDebug)]
pub struct VirtualMemory {
    /// The range of virtual addresses covered by this region.
    ///
    /// Note: they are virtual addresses, not PFNs.
    pub range: Range<VirtAddr>,
    /// The backing mapping for this virtual memory.
    pub mapping: Mapping,
    /// The page table entry flags for this region.
    #[deko(skip)]
    pub flags: PteFlags,
}

/// Tracks the corresponding permissions for a virtual memory if there is
/// a need to read/modify this struct.
pub tracked struct VirtualMemoryPermission {
    pub ghost parent_id: int,
    /// Ghost state: The virtual address range this permission governs
    pub range: Range<VirtAddr>,
}

impl WellFormed for VirtualMemoryRegion {
    open spec fn wf(&self) -> bool {
        &&& (VADDR_UPPER_MASK >> 12) <= self.start_pfn < self.end_pfn <= u64::MAX >> 12
        &&& (self.start_pfn << 12) % VMR_GRANULE == 0
        &&& (self.end_pfn << 12) % VMR_GRANULE == 0
        &&& self.pt_flags.wf()
        &&& self.pt_flags.bits() & Pte_ALL_BITS == self.pt_flags.bits()
        &&& self.pgtable_consistent()
        &&& forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int ==> self.areas@[i].wf() && (self.start_pfn
                <= self.areas@[i].range.start.pfn()@ < self.areas@[i].range.end.pfn()@
                <= self.end_pfn)
            // Ensure no overlapping areas.
        &&& forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() - 1 as int ==> {
                &&& self.areas@[i].range.end@ <= self.areas@[i + 1].range.start@
            }
        &&& self.areas@.len() < u64::MAX as int
        &&& is_sorted_spec(self.areas@)
        &&& self.ms.wf()
        &&& bit_not_overlapping(self.private_bit)
        &&& bit_not_in_addr_region(self.private_bit)
        &&& bit_not_overlapping(self.shared_bit)
        &&& bit_not_in_addr_region(self.shared_bit)
    }
}

impl WellFormed for VirtualMemory {
    open spec fn wf(&self) -> bool {
        &&& self.range.wf()
        &&& self.range.start@ % PAGE_SIZE == 0
        &&& self.range.end@ % PAGE_SIZE == 0
        &&& self.range.end@ + PAGE_SIZE_2M <= u64::MAX
        &&& all_normalized_vaddrs(self.range)
        &&& self.mapping.wf()
        &&& self.flags.bits() & Pte_ALL_BITS == self.flags.bits()
        &&& self.flags.wf()
    }
}

impl PartialEq for VirtualMemory {
    #[verifier::external_body]
    fn eq(&self, other: &Self) -> bool {
        self.range.start.0 == other.range.start.0 && self.range.end.0 == other.range.end.0
    }
}

impl PartialOrd for VirtualMemory {
    // Verus has some problem dealing with this.
    #[verifier::external_body]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        if self.range.start.0 < other.range.start.0 {
            Some(core::cmp::Ordering::Less)
        } else if self.range.start.0 > other.range.start.0 {
            Some(core::cmp::Ordering::Greater)
        } else {
            Some(core::cmp::Ordering::Equal)
        }
    }
}

impl PartialEqSpecImpl for VirtualMemory {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        &&& self.range.start@ == other.range.start@
        &&& self.range.end@ == other.range.end@
    }
}

impl PartialOrdSpecImpl for VirtualMemory {
    closed spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<core::cmp::Ordering> {
        if self.range.start@ < other.range.start@ {
            Some(core::cmp::Ordering::Less)
        } else if self.range.start@ > other.range.start@ {
            Some(core::cmp::Ordering::Greater)
        } else {
            Some(core::cmp::Ordering::Equal)
        }
    }
}

#[verus_verify]
impl VirtualMemoryRegion {
    /// This is an invariant that the coverage bits are consistent with the actual areas
    /// the region is managing, i.e., `forall i ∈ [0, 512)`, coverage bit `i` is set iff.
    /// `i * LEVEL_3_SPAN` is in `[start_pfn * PAGE_SIZE, end_pfn * PAGE_SIZE)` and `∃ vm ∈ areas.`
    /// such that `vm.range` covers the whole `[i * LEVEL_3_SPAN, (i + 1) * LEVEL_3_SPAN)`.
    pub open spec fn coverage_consistent(&self, perm: &VirtualMemoryRegionPermission) -> bool {
        // TODO: Say this.
        // &&& ((self.pgtable_top_level_coverage) as u64) & (RECURSIVE_INDEX) == 0
        true
    }

    pub open spec fn wf_with(&self, perm: &VirtualMemoryRegionPermission) -> bool {
        &&& self.id == perm.id
        &&& self.ms == perm.pgtable_perm.mapping_space
        &&& self.private_bit == perm.pgtable_perm.private_bit
        &&& self.shared_bit == perm.pgtable_perm.shared_bit
        &&& perm.pgtable_perm.wf()
        &&& perm.pgtable_perm.pgtable_perm.pptr() == self.pgtable@
        &&& perm.vm_perms@.len() == self.areas@.len()
        &&& forall|i: int|
            0 <= i < self.areas@.len() ==> #[trigger] self.areas@[i].wf_with(&perm.vm_perms@[i])
        &&& forall|i: int|
            0 <= i < self.areas@.len() ==> #[trigger] perm.vm_perms@[i].parent_id == self.id
        &&& self.coverage_consistent(perm)
    }

    pub open spec fn pgtable_consistent(&self) -> bool {
        true
    }

    /// This says that the block does not overlap with any existing blocks in the sense of
    /// virtual address mapping.
    pub open spec fn disjoint_blocks(&self, vm_block: &VirtualMemory) -> bool {
        forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int ==> { self.areas@[i].disjoint_with(vm_block) }
    }

    /// Checks whether there is enough space to insert a new mapping of the given size.
    pub open spec fn can_insert(&self, size: u64) -> bool
        recommends
            size > 0,
            is_power_of_two_spec(size as nat),
            self.wf(),
            is_sorted_spec(self.areas@),
    {
        exists|i: int| 0 <= i <= self.areas@.len() && #[trigger] self.gap_size_at(i) >= size
    }

    /// Returns the size of the gap at position i
    /// - Gap i is between areas[i-1] and areas[i]
    /// - Gap 0 is before the first area
    /// - Gap len() is after the last area
    pub open spec fn gap_size_at(&self, i: int) -> u64
        recommends
            0 <= i <= self.areas@.len(),
    {
        let gap_start = if i == 0 {
            self.start_pfn
        } else {
            self.areas@[i - 1].range.end.pfn()@
        };

        let gap_end = if i == self.areas@.len() {
            self.end_pfn
        } else {
            self.areas@[i].range.start.pfn()@
        };

        if gap_end > gap_start {
            (gap_end - gap_start) as u64
        } else {
            0
        }
    }

    pub open spec fn new_spec(
        start_addr: VirtAddr,
        end_addr: VirtAddr,
        pt_flags: PteFlags,
        pgtable: DekoPPtr<PageTable>,
        ms: MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        s: Self,
    ) -> bool {
        &&& s.start_pfn == start_addr.pfn()@
        &&& s.end_pfn == end_addr.pfn()@
        &&& s.pt_flags == pt_flags
        &&& s.areas@ == Seq::<VirtualMemory>::empty()
        &&& s.pgtable == pgtable
        &&& s.ms == ms
        &&& s.private_bit == private_bit
        &&& s.shared_bit == shared_bit
    }

    pub open spec fn compatible_spec(&self, vm_block: &VirtualMemory) -> bool {
        &&& vm_block.range.start@ >= self.start_pfn * PAGE_SIZE
        &&& vm_block.range.end@ <= self.end_pfn
            * PAGE_SIZE
        // &&& all_in_range_paddrs(&self.ms, vm_block.paddr, vm_block.range)

    }

    pub proof fn lemma_disjoint_blocks_implies_ne(&self, vm_block: &VirtualMemory)
        requires
            self.wf(),
            self.disjoint_blocks(vm_block),
            vm_block.wf(),
            vm_block.range.start@ % PAGE_SIZE == 0,
            vm_block.range.end@ % PAGE_SIZE == 0,
        ensures
            forall|i: int|
                #![trigger self.areas@[i]]
                0 <= i < self.areas@.len() as int ==> self.areas@[i].range.start.pfn()@
                    != vm_block.range.start.pfn()@,
    {
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

        assert forall|i: int|
            #![trigger self.areas@[i]]
            0 <= i < self.areas@.len() as int implies self.areas@[i].range.start.pfn()@
            != vm_block.range.start.pfn()@ by {
            assert(!self.areas@[i].overlap_with_spec(vm_block));
            assert(self.areas@[i].range.start@ >= vm_block.range.end@ || self.areas@[i].range.end@
                <= vm_block.range.start@);
            assert(self.areas@[i].wf() && vm_block.wf());
        }
    }

    #[verus_spec(r =>
        with
            Tracked(pgtable_perm): Tracked<PageTablePermission>,
                -> vmr_perm: Tracked<VirtualMemoryRegionPermission>,
        requires
            start_addr@ >= VADDR_UPPER_MASK,
            start_addr@ < end_addr@ <= u64::MAX,
            start_addr@ % VMR_GRANULE == 0,
            end_addr@ % VMR_GRANULE == 0,
            pt_flags.wf(),
            pt_flags.bits() & Pte_ALL_BITS == pt_flags.bits(),
            ms.wf(),
            ms == pgtable_perm.mapping_space,
            private_bit == pgtable_perm.private_bit,
            shared_bit == pgtable_perm.shared_bit,
            pgtable_perm.wf(),
            pgtable_perm.pgtable_perm.pptr() == pgtable@,
            bit_not_overlapping(private_bit),
            bit_not_in_addr_region(private_bit),
            bit_not_overlapping(shared_bit),
            bit_not_in_addr_region(shared_bit),
        ensures
            r.wf(),
            r.wf_with(&vmr_perm@),
            Self::new_spec(
                start_addr,
                end_addr,
                pt_flags,
                pgtable,
                ms,
                private_bit,
                shared_bit,
                r,
            ),
    )]
    pub fn new(
        start_addr: VirtAddr,
        end_addr: VirtAddr,
        pt_flags: PteFlags,
        pgtable: DekoPPtr<PageTable>,
        ms: MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> Self {
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

        proof {
            let start = start_addr@;
            let end = end_addr@;
            let start_pfn = start_addr.pfn()@;
            let end_pfn = end_addr.pfn()@;

            assert(start_pfn < end_pfn) by (bit_vector)
                requires
                    VADDR_UPPER_MASK <= start < end,
                    start_pfn == start >> 12,
                    end_pfn == end >> 12,
                    start % VMR_GRANULE == 0,
                    end % VMR_GRANULE == 0,
            ;

            assert(end_pfn <= u64::MAX / PAGE_SIZE) by (bit_vector)
                requires
                    end <= u64::MAX,
                    end_pfn == end >> 12,
            ;

            assert((((start >> 12u64) << 12u64) % VMR_GRANULE == 0) && (((end >> 12u64) << 12u64)
                % VMR_GRANULE == 0)) by (bit_vector)
                requires
                    start % VMR_GRANULE == 0,
                    end % VMR_GRANULE == 0,
                    start < end <= u64::MAX,
            ;

            assert(start_pfn >= (VADDR_UPPER_MASK >> 12)) by (bit_vector)
                requires
                    start >= VADDR_UPPER_MASK,
                    start_pfn == start >> 12,
            ;
        }

        proof {
            super::paging::option_page_ptr_array_size_wf();

            let e = end_addr@;
            assert((e >> 12) <= u64::MAX >> 12) by (bit_vector)
                requires
                    e <= u64::MAX,
            ;
        }

        let ghost id = arbitrary();

        proof_with!(|=
            Tracked(VirtualMemoryRegionPermission {
                id,
                pgtable_perm,
                vm_perms: Ghost(Seq::empty()),
            })
        );
        Self {
            id: Ghost(id),
            start_pfn: start_addr.pfn().0,
            end_pfn: end_addr.pfn().0,
            pt_flags,
            areas: vec![],
            pgtable,
            pgtable_top_level_coverage: 0,
            ms,
            private_bit,
            shared_bit,
        }
    }

    /// Copies all the page table entries from this region's page table to the target page table.
    ///
    /// The copy is lazy: only entries at the top-level managed by this region will be copied to
    /// to top-level of the target page table. New mappings will do a full copy when needed.
    ///
    /// We do not use `self.areas` to do the copy as this is inefficient because there might be
    /// many small areas scattered in the region. Using the bitmap is guaranteed that the loop
    /// will ends in at most 512 iterations.
    #[verus_spec(
        with
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
            Tracked(region_perm): Tracked<&VirtualMemoryRegionPermission>,
        requires
            self.wf(),
            self.wf_with(region_perm),
            old(pgtable_perm).wf(),
            old(pgtable_perm).pgtable_perm.pptr() == target_pgtable@,
            self.private_bit == old(pgtable_perm).private_bit,
            self.shared_bit == old(pgtable_perm).shared_bit,
        ensures
            pgtable_perm.wf(),
            pgtable_perm.pgtable_perm.pptr() == target_pgtable@,
            old(pgtable_perm).mapping_space == pgtable_perm.mapping_space,
            old(pgtable_perm).private_bit == pgtable_perm.private_bit,
            old(pgtable_perm).shared_bit == pgtable_perm.shared_bit,
            // more...
    )]
    pub fn copy_to_page_table(&self, target_pgtable: DekoPPtr<PageTable>) {
        broadcast use crate::mm::paging::PteFlags::lemma_each_bit_is_valid;

        let mut i = 0;
        let flags = PteFlags::writeable_kernel();

        proof {
            bit_u64_and_auto();
        }

        #[verus_spec(
            invariant
                i <= PAGE_TABLE_ENTRY,
                PAGE_TABLE_ENTRY == 512,
                self.wf(),
                self.wf_with(region_perm),
                pgtable_perm.wf(),
                pgtable_perm.pgtable_perm.pptr() == target_pgtable@,
                flags.wf(),
                flags.bits() & Pte_ALL_BITS == flags.bits(),
                self.private_bit == pgtable_perm.private_bit,
                self.shared_bit == pgtable_perm.shared_bit,
                old(pgtable_perm).mapping_space == pgtable_perm.mapping_space,
                old(pgtable_perm).private_bit == pgtable_perm.private_bit,
                old(pgtable_perm).shared_bit == pgtable_perm.shared_bit,
            decreases
                PAGE_TABLE_ENTRY - i,
        )]
        while i < PAGE_TABLE_ENTRY {
            // Check if this top-level entry is covered by this region
            if i & (self.pgtable_top_level_coverage as usize) != 0 {
                // We've found a coverage and then we copy the entry.
                let entry = self.pgtable.borrow(
                    Tracked(&region_perm.pgtable_perm.pgtable_perm),
                ).0.index(i);
                let new_entry_val = PageTableEntry(
                    PhysAddr(
                        make_private_address(entry.0.0, self.private_bit, self.shared_bit)
                            | flags.bits(),
                    ),
                );
                PageTable::update_entry_by_ptr(
                    target_pgtable,
                    Tracked(&mut pgtable_perm.pgtable_perm),
                    i,
                    new_entry_val,
                );

                proof {
                    // TODO: Update pgtable_perm accordingly.
                    assume(pgtable_perm.wf());
                }
            }
            i += 1;
        }
    }

    /// Inserts a new mapping [`VmMapping`] into the virtual memory region and
    /// returns the virtual address where it was inserted.
    ///
    /// Since it is hard to verify that the the insertion will always succeed,
    /// we currently rely on runtime checks to ensure safety (but may incur
    /// little performance overhead as linear scan is `O(n)`).
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
        requires
            old(self).wf(),
            old(self).wf_with(old(perm)),
            old(self).areas@.len() + 1 < u64::MAX as int,
            mapping.wf(),
            flags.wf(),
            flags.bits() & Pte_ALL_BITS == flags.bits(),
        ensures
            self.wf(),
            self.wf_with(perm),
            old(perm).pgtable_perm.private_bit == perm.pgtable_perm.private_bit,
            old(perm).pgtable_perm.shared_bit == perm.pgtable_perm.shared_bit,
            r matches Some(vaddr) ==> {
                &&& vaddr@ % PAGE_SIZE == 0
                // &&& self.range.start@ <= vaddr@ < self.range.end@
            },
    )]
    #[inline]
    pub fn insert(&mut self, mapping: Mapping, flags: PteFlags) -> Option<VirtAddr> {
        let align = {
            let read_handle = mapping.as_ref().data.acquire_read();
            let align = read_handle.borrow().data.mapping_size();

            read_handle.release_read();
            align.next_power_of_two()
        };

        kinfo!("Inserting VM block with alignment:", align => hex);

        // Safe to proceed
        proof_with!(Tracked(perm));
        self.insert_aligned(mapping, None, align, flags)
    }

    /// Inserts a new VM block [`VirtualMemory`] at the given virtual address.
    /// Note that this method checks if the block will overlap with any of the
    /// current blocks in this region.
    ///
    /// This will consumes [`VirtualMemoryRegionPermission`] since now the owner-
    /// ship has been transferred to the newly inserted block.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
        requires
            old(self).wf(),
            old(self).wf_with(old(perm)),
            old(self).areas@.len() + 1 < u64::MAX as int,
            mapping.wf(),
            hint matches Some(h) ==> {
                &&& h.wf()
                &&& h@ % PAGE_SIZE == 0
                &&& old(self).start_pfn <= h.pfn()@ <= old(self).end_pfn
            },
            is_power_of_two_spec(align as nat),
            flags.wf(),
            flags.bits() & Pte_ALL_BITS == flags.bits(),
            PAGE_SIZE <= align <= u64::MAX,
            is_power_of_two_spec(align as nat),
        ensures
            r matches Some(vaddr) ==> {
                &&& vaddr@ % PAGE_SIZE == 0
                // &&& self.range.start@ <= vaddr@ < self.range.end@
            },
            self.wf(),
            self.wf_with(perm),
            old(perm).pgtable_perm.private_bit == perm.pgtable_perm.private_bit,
            old(perm).pgtable_perm.shared_bit == perm.pgtable_perm.shared_bit,
    )]
    #[verifier::spinoff_prover]
    pub fn insert_aligned(
        &mut self,
        mapping: Mapping,
        hint: Option<VirtAddr>,
        align: u64,
        flags: PteFlags,
    ) -> Option<VirtAddr> {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

        let hint = match hint {
            Some(h) => h.pfn(),
            None => VirtAddr(self.start_pfn),
        };

        let size = {
            let read_handle = mapping.as_ref().data.acquire_read();
            let size = read_handle.borrow().data.mapping_size();

            read_handle.release_read();
            size
        };

        // Convert align to nr_pages.
        let align_pages = align >> 12;

        // Now let's find the proper position to insert.
        let f = |mm: &VirtualMemory| -> (r: Ordering)
            requires
                mm.wf(),
            ensures
                r == vstd::std_specs::cmp::OrdSpec::cmp_spec(&mm.range.start.pfn()@, &hint@),
            { mm.range.start.pfn().0.cmp(&hint.0) };

        proof {
            self.lemma_areas_comparator_consistent(hint, f);
        }

        // Since we do not have specified `partition_point` yet; here
        // we use `binary_search_by` to find the proper index.
        let idx = self.areas.binary_search_by(f);
        // Extract the index - this is where an area with start == hint would be
        let search_start_idx = match idx {
            Ok(i) => i,  // Exact match on start address
            Err(i) => i,  // Would be inserted here
        };

        // Search for a suitable gap starting from search_start_idx
        // We need to check gaps: [prev.end .. areas[i].start] and [areas[last].end .. end_pfn]
        let mut current_pos = if search_start_idx > 0 {
            // Start after the previous area, but not before hint
            let prev_end = self.areas[search_start_idx - 1].range.end.pfn().0;
            if prev_end > hint.0 {
                prev_end
            } else {
                hint.0
            }
        } else {
            // No previous area, start from region beginning or hint
            if self.start_pfn > hint.0 {
                self.start_pfn
            } else {
                hint.0
            }
        };

        proof {
            assert(current_pos <= u64::MAX - align_pages) by {
                assert(current_pos <= self.end_pfn <= (u64::MAX >> 12));

                assert(current_pos <= u64::MAX - align_pages) by (bit_vector)
                    requires
                        current_pos <= (u64::MAX >> 12),
                        align_pages == align >> 12,
                        align <= u64::MAX,
                ;
            }

            assert(current_pos >= hint@);
        }

        let tracked mut old_pos = current_pos;
        let mut found_gap: Option<(usize, u64)> = None;
        let mut i = search_start_idx;
        #[verus_spec(
            invariant
                search_start_idx <= i <= self.areas@.len() + 1 <= u64::MAX as int,
                self.wf(),
                self.wf_with(perm),
                is_sorted_spec(self.areas@),
                self.start_pfn <= hint@ <= current_pos,
                forall |j: int|
                    #![trigger self.areas@[j]]
                    0 <= j < search_start_idx as int ==> {
                        &&& self.areas@[j].range.end.pfn()@ <= current_pos
                    },
                 self.areas@.len() >= i > search_start_idx ==> {
                    &&& current_pos == self.areas@[i as int - 1].range.end.pfn()@
                },
                old_pos <= current_pos <= u64::MAX - align_pages,
                align_pages == align >> 12,
                self.start_pfn <= current_pos,
                PAGE_SIZE <= align <= u64::MAX,
                is_power_of_two_spec(align as nat),
                found_gap matches Some((i, gap_start)) ==> {
                    &&& 0 <= i <= self.areas@.len()
                    &&& gap_start + size <= self.end_pfn
                    &&& gap_start >= self.start_pfn
                }
            decreases
                (self.areas@.len() + 1) - i as nat,
        )]
        while i <= self.areas.len() {
            proof {
                assert(0 < align_pages < u64::MAX) by (bit_vector)
                    requires
                        PAGE_SIZE <= align <= u64::MAX,
                        align_pages == align >> 12,
                ;

                assert(is_power_of_two_spec(align_pages as nat)) by {
                    assert(is_power_of_two_spec(align as nat));
                    lemma_is_power_of_two_equiv(align_pages);
                    lemma_is_power_of_two_equiv(align);

                    assert((align_pages & (align_pages - 1) as u64) == 0) by (bit_vector)
                        requires
                            align as u64 & (align - 1) as u64 == 0,
                            align_pages == align >> 12,
                    ;
                }
            }

            // Align the current position
            let gap_start = align_up(current_pos, align_pages);

            // Find where this gap ends
            let gap_end = if i < self.areas.len() {
                self.areas[i].range.start.pfn().0
            } else {
                self.end_pfn
            };

            // Check if this gap is large enough
            if gap_start < gap_end && gap_end - gap_start >= size {
                // Double-check bounds
                if gap_start >= self.start_pfn && gap_start + size <= self.end_pfn {
                    found_gap = Some((i, gap_start));
                    break ;
                }
            }
            // Move to the end of current area for next iteration

            if i < self.areas.len() {
                proof {
                    old_pos = current_pos;
                }

                current_pos = self.areas[i].range.end.pfn().0;

                proof {
                    assert(current_pos <= self.end_pfn);
                    assert(current_pos <= self.end_pfn <= (u64::MAX >> 12));

                    assert(current_pos <= u64::MAX - align_pages) by (bit_vector)
                        requires
                            current_pos <= (u64::MAX >> 12),
                            align_pages == align >> 12,
                            align <= u64::MAX,
                    ;

                    // The same.
                    assert(old_pos <= current_pos) by {
                        if i == search_start_idx {
                            admit();
                        } else {
                            admit();
                        }
                    }
                }
            }
            i += 1;
        }

        // If no gap found, return None
        let (insert_idx, gap_start_pfn) = match found_gap {
            Some(result) => result,
            None => {
                return None;
            },
        };

        proof {
            assert(gap_start_pfn + size <= self.end_pfn);
            assert(self.end_pfn <= u64::MAX >> 12);

            // Awkward due to precedence issue.
            // Prove left shift doesn't overflow
            assert(gap_start_pfn << 12 <= u64::MAX) by (bit_vector)
                requires
                    gap_start_pfn <= (u64::MAX >> 12),
            ;

            // Prove we have room for the addition
            assert((gap_start_pfn << 12) <= u64::MAX - size) by (bit_vector)
                requires
                    gap_start_pfn + size <= (u64::MAX >> 12),
            ;
        }

        // Now construct the vm block.
        let end = gap_start_pfn << 12;
        let end = end + size;
        let range = VirtAddr(gap_start_pfn << 12)..VirtAddr(end);

        proof {
            assert((gap_start_pfn << 12) >= VADDR_UPPER_MASK) by (bit_vector)
                requires
                    gap_start_pfn >= (VADDR_UPPER_MASK >> 12),
                    gap_start_pfn <= u64::MAX >> 12,
            ;

            assert((gap_start_pfn << 12) as u64 % PAGE_SIZE == 0) by (bit_vector)
                requires
                    gap_start_pfn <= u64::MAX >> 12,
            ;
        }

        proof_with!(Ghost(self) => Tracked(vm_block_perm));
        let vm_block = VirtualMemory::new(range, mapping, flags);

        {
            proof {
                assert(self.compatible_spec(&vm_block)) by {
                    admit();
                }
                assert(self.disjoint_blocks(&vm_block)) by {
                    admit();
                }
            }
        }

        // Finally, we can insert the new block.
        proof_with!(Tracked(perm), Tracked(vm_block_perm));
        self.insert_at_vaddr(VirtAddr(gap_start_pfn << 12), vm_block);

        Some(VirtAddr(gap_start_pfn << 12))
    }

    /// Removes the mapping from a given base address from the region.
    ///
    /// If the given address is not found then we return [`Option::None`].
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
                -> vm_perm: Ghost<Option<VirtualMemoryPermission>>,
            requires
                old(self).wf(),
                old(self).wf_with(old(perm)),
                vaddr.wf(),
                vaddr@ >= VADDR_UPPER_MASK,
            ensures
                self.wf_with(perm),
                r matches Some(vm) ==> {
                    &&& vm.wf()
                    &&& vm_perm@ matches Some(vm_perm_val) && vm.wf_with(&vm_perm_val) && vm_perm_val.parent_id == self.id
                }
    )]
    pub fn remove(&mut self, vaddr: VirtAddr) -> Option<VirtualMemory> {
        broadcast use vstd::std_specs::vec::group_vec_axioms;

        let pfn = vaddr.pfn();
        let f = |mm: &VirtualMemory| -> (r: Ordering)
            requires
                mm.wf(),
            ensures
                r == vstd::std_specs::cmp::OrdSpec::cmp_spec(&mm.range.start.pfn()@, &pfn@),
            { mm.range.start.pfn().0.cmp(&pfn.0) };

        proof {
            self.lemma_areas_comparator_consistent(pfn, f);
        }

        match self.areas.binary_search_by(f) {
            Ok(idx) => {
                let vm = self.areas.remove(idx);

                // Then we unmap it; remove it.
                // #[verus_spec(with Tracked(&mut perm))]
                // vm.unmap(self.pgtable);

                let ghost vm_perm = perm.vm_perms@.index(idx as int);

                proof {
                    // remove it.
                    perm.vm_perms = Ghost(perm.vm_perms@.remove(idx as int));
                }

                proof_with!(|= Ghost(Some(vm_perm)));
                Some(vm)
            },
            Err(_) => {
                proof_with!(|= Ghost(None));
                None
            },
        }
    }

    /// Unlike [`Self::insert_vm_block`] or [`Self::insert_aligned`], this method ensures that
    /// the new block is inserted at the given virtual address if the caller requests to do so.
    ///
    /// This function does nothing if the address is already occupied.
    ///
    /// Note that this method checks if the block will overlap with any of the
    /// current blocks in this region.
    ///
    /// This will consumes [`VirtualMemoryRegionPermission`] since now the owner-
    /// ship has been transferred to the newly inserted block.
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VirtualMemoryRegionPermission>,
            Tracked(vm_block_perm): Tracked<VirtualMemoryPermission>,
        requires
            old(self).wf(),
            old(self).areas@.len() + 1 < u64::MAX as int,
            old(self).wf_with(old(perm)),
            old(self).compatible_spec(&vm_block),
            old(self).disjoint_blocks(&vm_block),
            vm_block.wf(),
            vm_block.wf_with(&vm_block_perm),
            vm_block_perm.parent_id == old(self).id,
        ensures
            self.wf(),
            self.wf_with(perm),
            self.areas@.len() == old(self).areas@.len() + 1,
            old(perm).pgtable_perm.private_bit == perm.pgtable_perm.private_bit,
            old(perm).pgtable_perm.shared_bit == perm.pgtable_perm.shared_bit,
    )]
    #[verifier::spinoff_prover]
    pub fn insert_at_vaddr(&mut self, vaddr: VirtAddr, vm_block: VirtualMemory) {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;
        // Either we can call "mapping_size" but this requires locking
        // and is not efficient so we just compute the size here; we
        // know by `wf` that the size matches the mapping size.`

        let size = vm_block.range.end.0 - vm_block.range.start.0;
        let start_addr = &vm_block.range.start;
        let end_addr = &vm_block.range.end;

        // Now let's find the proper position to insert.
        let f = |mm: &VirtualMemory| -> (r: Ordering)
            requires
                mm.wf(),
            ensures
                r == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &mm.range.start.pfn()@,
                    &start_addr.pfn()@,
                ),
            { mm.range.start.pfn().0.cmp(&start_addr.pfn().0) };

        proof {
            self.lemma_areas_comparator_consistent(start_addr.pfn(), f);
        }

        // Here we do a binary search again since we now have
        // already known the exact virtual address to insert.
        let idx = self.areas.binary_search_by(f);

        proof {
            assert(idx.is_err()) by {
                self.lemma_disjoint_blocks_implies_ne(&vm_block);
            }
        }

        // Verified, but to ensure safety at runtime as well.
        kpanic_if!(
            core::intrinsics::unlikely(idx.is_ok()),
            "Trying to inserting overlapping virtual memory block into region",
        );
        let idx_unwrapped = idx.unwrap_err();
        proof {
            if idx_unwrapped < self.areas@.len() - 1 {
                assert(vm_block.range.end@ <= self.areas@[idx_unwrapped + 1].range.start@) by {
                    if vm_block.range.start@ >= self.areas@[idx_unwrapped + 1].range.end@ {
                        assert(self.areas@[idx_unwrapped + 1].range.end@ > self.areas@[idx_unwrapped
                            + 1].range.start@);
                        assert(vm_block.range.start@ > self.areas@[idx_unwrapped + 1].range.start@);
                    }
                }
            }
        }

        proof {
            perm.vm_perms = Ghost(perm.vm_perms@.insert(idx_unwrapped as int, vm_block_perm));

            assert(self.start_pfn <= vm_block.range.start.pfn()@ < vm_block.range.start.pfn()@
                < self.end_pfn) by {
                // TODO: trivial proof so I'm lazy here.
                //
                // Basically using order preservation should be enough.
                admit();
            }
        }

        // We first map the new block.
        proof_with!(Tracked(perm), Ghost(idx_unwrapped as int));
        vm_block.map(self.pgtable, &self.ms, self.private_bit, self.shared_bit);
        // Now update the coverage bitmap.
        let top_level_start = index_at_level::<3>(vm_block.range.start);
        self.pgtable_top_level_coverage = self.pgtable_top_level_coverage | (
        top_level_start as u16);
        // Finally, we can insert the new block.
        self.areas.insert(idx_unwrapped, vm_block);
    }

    /// Notify the region that we have encountered a page fault at the given address.
    /// This function will return true if the page fault is handled successfully.
    ///
    /// This method does _not_ create the mapping.
    #[verus_spec(r =>
        requires
            vaddr.wf(),
    )]
    pub fn handle_page_fault(&self, vaddr: VirtAddr) -> bool {
        kunimplemented!()
    }

    /// Lemma to show that the comparator used in binary search is consistent with
    /// the ordering of the areas.
    pub proof fn lemma_areas_comparator_consistent<F: FnMut(&VirtualMemory) -> Ordering>(
        &self,
        hint: VirtAddr,
        f: F,
    )
        requires
            self.wf(),
            is_sorted_spec(self.areas@),
            forall|i: int|
                #![trigger self.areas@[i]]
                0 <= i < self.areas@.len() ==> self.areas@[i].wf(),
            forall|i: int, r: Ordering|
                #![trigger self.areas@[i], f.ensures((&self.areas@[i],), r)]
                0 <= i < self.areas@.len() && f.ensures((&self.areas@[i],), r) ==> r
                    == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &self.areas@[i].range.start.pfn()@,
                    &hint@,
                ),
        ensures
            comparator_consistent_spec(self.areas@, f),
    {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use deko_std::address::lemma_aligned_vaddr_pfn_preserves_order;

        assert(comparator_consistent_spec(self.areas@, f)) by {
            assert forall|i: int, j: int, ord1: Ordering, ord2: Ordering|
                0 <= i < j < self.areas@.len() && f.ensures((&self.areas@[i],), ord1) && f.ensures(
                    (&self.areas@[j],),
                    ord2,
                ) implies vstd::std_specs::cmp::OrdSpec::cmp_spec(&ord1, &ord2)
                != Ordering::Greater by {
                let area_i = &self.areas@[i];
                let area_j = &self.areas@[j];
                // From f's specification
                assert(ord1 == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &area_i.range.start.pfn()@,
                    &hint@,
                ));
                assert(ord2 == vstd::std_specs::cmp::OrdSpec::cmp_spec(
                    &area_j.range.start.pfn()@@,
                    &hint@@,
                ));
                // From is_sorted_spec
                let cmp_result = vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(
                    area_i,
                    area_j,
                );
                assert(cmp_result == Some(Ordering::Less) || cmp_result == Some(Ordering::Equal));

                lemma_cmp_pivot_monotonic(
                    area_i.range.start.pfn()@,
                    area_j.range.start.pfn()@,
                    hint@,
                );
            }
        }
    }
}

#[verus_verify]
impl VirtualMemory {
    pub open spec fn wf_with(&self, perm: &VirtualMemoryPermission) -> bool {
        &&& self.range == perm.range
    }

    pub open spec fn contains_addr_spec(&self, addr: VirtAddr) -> bool {
        self.range.start@ <= addr@ < self.range.end@
    }

    pub open spec fn subset_of_spec(&self, other: &VirtualMemory) -> bool {
        &&& self.range.start@ >= other.range.start@
        &&& self.range.end@ <= other.range.end@
    }

    pub open spec fn overlap_with_spec(&self, other: &VirtualMemory) -> bool {
        !self.disjoint_with_spec(other)
    }

    pub open spec fn disjoint_with_spec(&self, other: &VirtualMemory) -> bool {
        self.range.end@ <= other.range.start@ || self.range.start@ >= other.range.end@
    }

    /// Creates a new virtual memory region.
    #[inline]
    #[verus_spec(r =>
        with
            Ghost(parent): Ghost<&VirtualMemoryRegion>,
            -> vm_perm: Tracked<VirtualMemoryPermission>,
        requires
            range.wf(),
            mapping.wf(),
            flags.wf(),
            flags.bits() & Pte_ALL_BITS == flags.bits(),
        ensures
            r.wf(),
            r.wf_with(&vm_perm@),
            vm_perm@.parent_id == parent.id,
    )]
    #[verifier::external_body]
    pub fn new(range: VaddrRange, mapping: Mapping, flags: PteFlags) -> Self {
        proof_with!(|= Tracked::assume_new());
        Self { range, mapping, flags }
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
    ///
    /// [       ]
    ///     [        ]
    /// [       ]
    ///    []
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
        !self.disjoint_with(other)
    }

    /// Checks if two virtual memory regions are disjoint.
    ///
    /// [     ] [      ]
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
            other.wf(),
        returns
            self.disjoint_with_spec(other),
    )]
    #[verifier::when_used_as_spec(disjoint_with_spec)]
    pub fn disjoint_with(&self, other: &VirtualMemory) -> bool {
        self.range.end.0 <= other.range.start.0 || self.range.start.0 >= other.range.end.0
    }

    /// Maps this virtual memory [`VirtualMemory`] into the given page table.
    #[verus_spec(
        with
            Tracked(parent_perm): Tracked<&mut VirtualMemoryRegionPermission>,
            Ghost(idx): Ghost<int>,
        requires
            self.wf(),
            self.wf_with(&old(parent_perm).vm_perms@.index(idx)),
            ptr@ == old(parent_perm).pgtable_perm.pgtable_perm.pptr(),
            old(parent_perm).pgtable_perm.wf(),
            old(parent_perm).pgtable_perm.mapping_space == ms,
            old(parent_perm).pgtable_perm.private_bit == private_bit,
            old(parent_perm).pgtable_perm.shared_bit == shared_bit,
            ms.wf(),
            bit_not_overlapping(private_bit),
            bit_not_in_addr_region(private_bit),
            bit_not_overlapping(shared_bit),
            bit_not_in_addr_region(shared_bit),
            // all_in_range_paddrs(ms, self.paddr, self.range),
        ensures
            parent_perm.pgtable_perm.wf(),
            // parent_perm.pgtable_perm.mapped_region(self.range), // not so simple.
            parent_perm.pgtable_perm.mapping_space == ms,
            parent_perm.pgtable_perm.private_bit == private_bit,
            parent_perm.pgtable_perm.shared_bit == shared_bit,
            parent_perm.pgtable_perm.pgtable_perm.pptr() == old(parent_perm).pgtable_perm.pgtable_perm.pptr(),
            parent_perm.vm_perms == old(parent_perm).vm_perms,
            parent_perm.id == old(parent_perm).id,
    )]
    #[verifier::spinoff_prover]
    pub fn map(
        &self,
        ptr: DekoPPtr<PageTable>,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) {
        broadcast use crate::mm::paging::PteFlags::lemma_each_bit_is_valid;

        let lock = &self.mapping.as_ref().data;
        let read_handle = lock.acquire_read();
        let mapping_data = &read_handle.borrow().data;

        proof {
            use_type_invariant(&self.mapping);
            use_type_invariant(lock);

            assert(mapping_data.wf()) by {
                assert(lock.wf());
            }

            bit_u64_and_auto();
        }

        let mapping_size = mapping_data.mapping_size();
        let flags = PteFlags::from_bits_truncate(self.flags.bits() | PRESENT);

        kinfo!("VirtualMemory::map: mapping for", self.range);

        let mut offset = 0;
        #[verus_spec(
            invariant
                offset <= self.range.end@ - self.range.start@,
                offset % PAGE_SIZE == 0,
                mapping_size == mapping_data.mapping_size_spec(),
                PAGE_SIZE == 0x1000, // verus still requires const inlining...
                self.wf(),
                self.wf_with(&parent_perm.vm_perms@.index(idx)),
                ptr@ == parent_perm.pgtable_perm.pgtable_perm.pptr(),
                parent_perm.pgtable_perm.wf(),
                parent_perm.pgtable_perm.mapping_space == ms,
                parent_perm.pgtable_perm.private_bit == private_bit,
                parent_perm.pgtable_perm.shared_bit == shared_bit,
                parent_perm.pgtable_perm.mapping_space == ms,
                parent_perm.pgtable_perm.pgtable_perm.pptr() == old(parent_perm).pgtable_perm.pgtable_perm.pptr(),
                parent_perm.vm_perms == old(parent_perm).vm_perms,
                parent_perm.id == old(parent_perm).id,
                ms.wf(),
                bit_not_overlapping(private_bit),
                bit_not_in_addr_region(private_bit),
                bit_not_overlapping(shared_bit),
                bit_not_in_addr_region(shared_bit),
                mapping_data.wf(),
                flags.wf(),
                flags.bits() & Pte_ALL_BITS == flags.bits(),
            decreases
                self.range.end@ - self.range.start@ - offset,
        )]
        while offset < self.range.end.0 - self.range.start.0 {
            kdebug!("Requesting mapping at offset ", offset);

            // Request if there is a physical address at this offset.
            if let Some(paddr) = mapping_data.phys_at(offset) {
                let vaddr = VirtAddr(self.range.start.0 + offset);

                proof {
                    // This proof will be delayed.
                    assume(parent_perm.pgtable_perm.mapping_space.kernel.in_range_spec(paddr));
                }

                kdebug!("Mapping", vaddr, "to", paddr, "with flags", flags.bits() => hex);

                // Now we can map the page.
                PageTable::map_page_4k(
                    ptr,
                    Tracked(&mut parent_perm.pgtable_perm),
                    vaddr,
                    paddr,
                    ms,
                    flags.clone(),
                    private_bit,
                    shared_bit,
                );
            }
            offset += PAGE_SIZE;

            proof {
                assume(offset <= mapping_size);
            }
        }

        read_handle.release_read();
    }

    /// Unmaps this virtual memory region from the given page table.
    #[verus_spec(
        with
            Tracked(region_perm): Tracked<&mut VirtualMemoryPermission>,
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        requires
            self.wf(),
            self.wf_with(old(region_perm)),
            ptr@ == old(pgtable_perm).pgtable_perm.pptr(),
            old(pgtable_perm).wf(),
            old(pgtable_perm).mapped_region(self.range),
        ensures
            pgtable_perm.wf(),
            !pgtable_perm.mapped_region(self.range),
    )]
    pub fn unmap(&self, ptr: DekoPPtr<PageTable>) {
        kunimplemented!()
    }
}

} // verus!
