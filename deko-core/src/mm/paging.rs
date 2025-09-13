use deko_std::prelude::*;
use vstd::prelude::*;

use crate::mm::*;

deko_bitflags! {
    pub struct Pte: u64 {
        const PRESENT       = 0;
        const WRITABLE      = 1;
        const USER          = 2;
        // const PWT           = 3;
        // const PCD           = 4;
        const ACCESSED      = 5;
        const DIRTY         = 6;
        const HUGE          = 7;
        const GLOBAL        = 8;
        const NX            = 63;
    }
}

unsafe extern "C" {
    /// This is the initial page table set up before the stage2 code is even run.
    /// For interested readers please see `stage2.S` file for more information.
    ///
    /// This page table constructs a very simple identity mapping from virtual
    /// address to their physical address for the entire physical memory. Please
    /// also note that this papge table uses 2MB page for the PD level.
    ///
    /// It is always safe to access this page table since it is repr(C).
    #[link_name = "pgtable"]
    static mut initial_page_table: PageTable;
}

verus! {

// Note on the constants: Verus is having trouble verifying
// non-overflow/underflow of some arithmetic operations that
// involve constants and bit operations.
//
// We resort to hardcoding some of the results.
// FIXME: Make virtual address canonical (must be sign extended)
/// Size helpers
pub const SIZE_1K: u64 = 1024;

pub const SIZE_1M: u64 = SIZE_1K * 1024;

pub const SIZE_1G: u64 = SIZE_1M * 1024;

/// Pagesize definitions
pub const PAGE_SIZE: u64 = SIZE_1K * 4;

pub const PAGE_SIZE_2M: u64 = SIZE_1M * 2;

/// More size helpers
// pub const SIZE_LEVEL3: u64 = 1u64 << ((9 * 3) + 12);
// pub const SIZE_LEVEL2: u64 = 1u64 << ((9 * 2) + 12);
// pub const SIZE_LEVEL1: u64 = 1u64 << ((9 * 1) + 12);
// pub const SIZE_LEVEL0: u64 = 1u64 << ((9 * 0) + 12);
pub const SIZE_LEVEL3: u64 = 0x8000000000;

pub const SIZE_LEVEL2: u64 = 0x40000000;

pub const SIZE_LEVEL1: u64 = 0x200000;

pub const SIZE_LEVEL0: u64 = 0x1000;

// Stack definitions
pub const STACK_PAGES: u64 = 8;

pub const STACK_SIZE: u64 = PAGE_SIZE * STACK_PAGES;

pub const STACK_GUARD_SIZE: u64 = STACK_SIZE;

pub const STACK_TOTAL_SIZE: u64 = STACK_SIZE + STACK_GUARD_SIZE;

/// Level3 page-table index shared between all CPUs
pub const PGTABLE_LVL3_IDX_SHARED: u64 = 511;

/// Base Address of shared memory region
// pub const GLOBAL_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_SHARED << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const GLOBAL_BASE: VirtAddr = VirtAddr(0xFF8000000000);

pub const GLOBAL_MAPPING_SIZE: u64 = 256 * SIZE_1G;

/// Shared mappings region start
pub const GLOBAL_MAPPING_BASE: VirtAddr = VirtAddr(GLOBAL_BASE.0 + GLOBAL_MAPPING_SIZE);

/// Shared mappings region end
pub const GLOBAL_MAPPING_END: VirtAddr = VirtAddr(GLOBAL_MAPPING_BASE.0 + (SIZE_1G));

/// Mapping address for Hyper-V hypercall page.
pub const HYPERCALL_CODE_PAGE: VirtAddr = VirtAddr(GLOBAL_MAPPING_BASE.0 - PAGE_SIZE);

/// PerCPU mappings level 3 index
pub const PGTABLE_LVL3_IDX_PERCPU: u64 = 510;

/// Base Address of shared memory region
// pub const PERCPU_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_PERCPU << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const PERCPU_BASE: VirtAddr = VirtAddr(0xFFFF_FF00_0000_0000);

/// End Address of per-cpu memory region
pub const PERCPU_END: VirtAddr = VirtAddr(PERCPU_BASE.0 + (SIZE_LEVEL3));

/// PerCPU CAA mappings
pub const PERCPU_CAA_BASE: VirtAddr = VirtAddr(PERCPU_BASE.0 + (2 * SIZE_LEVEL0));

/// PerCPU VMSA mappings
pub const PERCPU_VMSA_BASE: VirtAddr = VirtAddr(PERCPU_BASE.0 + (4 * SIZE_LEVEL0));

/// Region for PerCPU Stacks
pub const PERCPU_STACKS_BASE: VirtAddr = VirtAddr(PERCPU_BASE.0 + (SIZE_LEVEL1));

/// Shadow stack address of the per-cpu init task
pub const SHADOW_STACKS_INIT_TASK: VirtAddr = PERCPU_STACKS_BASE;

/// Stack address to use during context switches
pub const CONTEXT_SWITCH_STACK: VirtAddr = VirtAddr(SHADOW_STACKS_INIT_TASK.0 + (STACK_TOTAL_SIZE));

/// Shadow stack address to use during context switches
pub const CONTEXT_SWITCH_SHADOW_STACK: VirtAddr = VirtAddr(
    CONTEXT_SWITCH_STACK.0 + (STACK_TOTAL_SIZE),
);

///  IST Stacks base address
pub const STACKS_IST_BASE: VirtAddr = VirtAddr(CONTEXT_SWITCH_SHADOW_STACK.0 + (STACK_TOTAL_SIZE));

/// DoubleFault IST stack base address
pub const STACK_IST_DF_BASE: VirtAddr = STACKS_IST_BASE;

/// DoubleFault ISST shadow stack base address
pub const SHADOW_STACK_ISST_DF_BASE: VirtAddr = VirtAddr(STACKS_IST_BASE.0 + (STACK_TOTAL_SIZE));

/// PerCPU XSave Context area base address
pub const XSAVE_AREA_BASE: VirtAddr = VirtAddr(SHADOW_STACK_ISST_DF_BASE.0 + (STACK_TOTAL_SIZE));

/// Base Address for temporary mappings - used by page-table guards
pub const PERCPU_TEMP_BASE: VirtAddr = VirtAddr(PERCPU_BASE.0 + (SIZE_LEVEL2));

// Below is space for 512 temporary 4k mappings and 511 temporary 2M mappings
/// Start and End for PAGE_SIZEed temporary mappings
pub const PERCPU_TEMP_BASE_4K: VirtAddr = PERCPU_TEMP_BASE;

pub const PERCPU_TEMP_END_4K: VirtAddr = VirtAddr(PERCPU_TEMP_BASE_4K.0 + (SIZE_LEVEL1));

/// Start and End for PAGE_SIZEed temporary mappings
pub const PERCPU_TEMP_BASE_2M: VirtAddr = VirtAddr(PERCPU_TEMP_BASE.0 + (SIZE_LEVEL1));

pub const PERCPU_TEMP_END_2M: VirtAddr = VirtAddr(PERCPU_TEMP_BASE.0 + (SIZE_LEVEL2));

/// Task mappings level 3 index
pub const PGTABLE_LVL3_IDX_PERTASK: u64 = 508;

/// Base address of task memory region
// pub const PERTASK_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_PERTASK << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const PERTASK_BASE: VirtAddr = VirtAddr(0xFE0000000000);

/// End address of task memory region
pub const PERTASK_END: VirtAddr = VirtAddr(PERTASK_BASE.0 + (SIZE_LEVEL3));

/// Page table self-map level 3 index
pub const PGTABLE_LVL3_IDX_PTE_SELFMAP: u64 = 493;

// pub const PTE_BASE: VirtAddr = VirtAddr(PGTABLE_LVL3_IDX_PTE_SELFMAP << ((3 * 9) + 12));
// FIXME: Hardcoded due to verus verification issues
pub const PTE_BASE: VirtAddr = VirtAddr(0xFFFFF68000000000);

//
// User-space mapping constants
//
/// Start of user memory address range
pub const USER_MEM_START: VirtAddr = VirtAddr(0);

/// End of user memory address range
pub const USER_MEM_END: VirtAddr = VirtAddr(USER_MEM_START.0 + (256 * SIZE_LEVEL3));

pub const PAGE_TABLE_ENTRY: usize = 0x200;

deko_bitflags_quick! {
    Pte,
    data: { PRESENT, WRITABLE, USER, ACCESSED, DIRTY, GLOBAL, NX },
    writeable: { PRESENT, USER, WRITABLE, ACCESSED, DIRTY },
    read_only: { PRESENT, USER, ACCESSED },
    kernel_code: { PRESENT, GLOBAL },
}

pub ghost struct DekoCpuPTOwner {
    pub cpu_id: u64,
    pub pgtable: u64,
}

impl WellFormed for DekoCpuPTOwner {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl DekoCpuPTOwner {
    pub open spec fn new(cpu_id: u64, pt: u64) -> Self {
        DekoCpuPTOwner { cpu_id, pgtable: pt }
    }

    pub open spec fn cpu_id(&self) -> u64 {
        self.cpu_id
    }

    pub open spec fn pgtable(&self) -> u64 {
        self.pgtable
    }
}

/// This function calculates the index at a given level L in the 4-level page table
/// hierarchy for a given virtual address `vaddr`.
#[inline]
pub fn index_at_level<const L: usize>(vaddr: VirtAddr) -> (r: usize)
    requires
        L < 4,
    ensures
        r < PAGE_TABLE_ENTRY,
{
    proof {
        assert forall|n: u64| n & 0x1ff < PAGE_TABLE_ENTRY by {
            bit_u64_and_auto();
        }
    }

    ((vaddr.0 >> (12 + L * 9)) & 0x1ff) as usize
}

/// ----- Utility function for manipoulating PTE values ------ ///
// marked as external_body because verus does not support complement.
#[inline(always)]
#[verifier::external_body]
pub fn strip_confidentiality_bits(paddr: u64) -> (r: u64) {
    paddr & !(PTE_MASK_PRIVATE.get().unwrap_or(&(1 << 51)))
}

// marked as external_body because verus does not support complement.
#[verifier::external_body]
#[inline(always)]
pub fn strip_shared_address_bits(paddr: u64) -> u64 {
    paddr & !(PTE_MASK_SHARED.get().unwrap())
}

/// Set address as private via mask.
#[verifier::external_body]
#[inline(always)]
fn make_private_address(paddr: u64) -> u64 {
    (strip_shared_address_bits(paddr) | (PTE_MASK_PRIVATE.get().unwrap_or(&(1 << 51))))
}

/// Set address as shared via mask.
#[verifier::external_body]
#[inline(always)]
fn make_shared_address(paddr: u64) -> u64 {
    (strip_confidentiality_bits(paddr) | PTE_MASK_SHARED.get().unwrap()).into()
}

/// A page table entry that is backed by a physical address.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct PageTableEntry(pub PhysAddr);

/// This struct contains a 4KiB array. Be careful when passing it around
/// as it might overflow the stack. The user should, at all times, pass
/// around a pointer to it instead of the struct itself.
#[repr(C)]
pub struct Page(pub Array<PageTableEntry, PAGE_TABLE_ENTRY>);

/// An alias to [`Page`] to indicate that it is a root page table (conceptually).
pub type PageTable = Page;

/// A page frame.
pub enum PageFrame {
    Frame4K(PhysAddr),
    Frame2M(PhysAddr),
    Frame1G(PhysAddr),
}

/// A mapping at a specific level in the page table hierarchy.
///
/// Please note that the wrapped pointer is the _virtual_address_ of the
/// corresponding PTEs at that level.
pub enum Mapping {
    Level3(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
    Level2(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
    Level1(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
    Level0(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
}

impl WellFormed for Mapping {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        let (pte_ptr, perm) = self.into_inner_spec();

        &&& pte_ptr@ == perm@.pptr()
        &&& perm@.is_init()
        &&& perm@.mem_wf()
        &&& perm@.wf()
        &&& pte_ptr.addr() + 0x1000 <= usize::MAX
    }
}

impl Mapping {
    #[verifier::inline]
    pub open spec fn into_inner_spec(self) -> (
        DekoPPtr<PageTableEntry>,
        Tracked<DekoPointsTo<PageTableEntry>>,
    ) {
        match self {
            Mapping::Level3(pte_ptr, perm) => (pte_ptr, perm),
            Mapping::Level2(pte_ptr, perm) => (pte_ptr, perm),
            Mapping::Level1(pte_ptr, perm) => (pte_ptr, perm),
            Mapping::Level0(pte_ptr, perm) => (pte_ptr, perm),
        }
    }

    /// Consumes this mapping, returning the underlying PTE pointer and permission.
    #[verifier::when_used_as_spec(into_inner_spec)]
    pub fn into_inner(self) -> (r: (
        DekoPPtr<PageTableEntry>,
        Tracked<DekoPointsTo<PageTableEntry>>,
    ))
        requires
            self.wf(),
        ensures
            r == self.into_inner_spec(),
            r.0@ == r.1@.pptr(),
            r.1@.is_init(),
            r.1@.mem_wf(),
            r.1@.wf(),
    {
        match self {
            Mapping::Level3(pte_ptr, perm) => (pte_ptr, perm),
            Mapping::Level2(pte_ptr, perm) => (pte_ptr, perm),
            Mapping::Level1(pte_ptr, perm) => (pte_ptr, perm),
            Mapping::Level0(pte_ptr, perm) => (pte_ptr, perm),
        }
    }

    #[verifier::inline]
    pub open spec fn level_spec(&self) -> usize {
        match self {
            Mapping::Level3(_, _) => 3,
            Mapping::Level2(_, _) => 2,
            Mapping::Level1(_, _) => 1,
            Mapping::Level0(_, _) => 0,
        }
    }

    #[verifier::when_used_as_spec(level_spec)]
    pub fn level(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.level_spec(),
    {
        match self {
            Mapping::Level3(_, _) => 3,
            Mapping::Level2(_, _) => 2,
            Mapping::Level1(_, _) => 1,
            Mapping::Level0(_, _) => 0,
        }
    }
}

impl WellFormed for PageTableEntry {
    // This needs to be stronger:
    //
    // a PTE might be convertible into a Page so that
    // we must at least guarantee that for non-leaf
    // PTEs, the page conversion should succeed.
    //
    // HACK: For now we just assume everything.
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

impl WellFormed for Page {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

impl WellFormed for PageFrame {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        match self {
            PageFrame::Frame4K(paddr) => paddr.wf(),
            PageFrame::Frame2M(paddr) => paddr.wf(),
            PageFrame::Frame1G(paddr) => paddr.wf(),
        }
    }
}

impl PageFrame {
    /// Get the address from the page frame, including the shared bit.
    pub fn page_frame(&self) -> PhysAddr {
        let paddr = match *self {
            Self::Frame4K(pa) => pa,
            Self::Frame2M(pa) => pa,
            Self::Frame1G(pa) => pa,
        };
        PhysAddr(strip_confidentiality_bits(paddr.0))
    }

    /// Get the address from the page frame, excluding the C/shared bit.
    pub fn address(&self) -> PhysAddr {
        PhysAddr(strip_shared_address_bits(self.page_frame().0))
    }
}

impl PageTableEntry {
    /// Get the address from the page table entry, including the shared bit.
    #[inline]
    pub fn page_frame(&self) -> PhysAddr {
        PhysAddr(strip_confidentiality_bits(self.0.0 & 0x000f_ffff_ffff_f000))
    }

    /// Get the address from the page table entry, excluding the C/shared bit.
    #[inline]
    pub fn address(&self) -> PhysAddr {
        PhysAddr(strip_shared_address_bits(self.page_frame().0))
    }

    pub closed spec fn is_valid_pte_spec(pte: DekoPointsTo<PageTableEntry>) -> bool {
        true
    }

    /// This function checks whether a given PTE is valid in the sense that
    /// it is either not present, or it is huge page so that we will need to
    /// take extra care when handling it.
    pub fn is_valid_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
        ensures
    // r == PageTableEntry::valid_pte_spec(*perm),

    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT) && !flags.contains(HUGE)
    }
}

impl PageTable {
    #[inline]
    /// Walk the page table at the given virtual address `vaddr` and return
    /// the mapping at the lowest possible level (in the sense that it is
    /// present in the entry).
    pub fn walk(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            pgtable@ == perm.pptr(),
            pgtable.addr() + 0x1000 <= usize::MAX,
            perm.wf(),
            perm.is_init(),
            perm.mem_wf(),
        ensures
            r.wf(),
    {
        Page::walk_level3(pgtable, Tracked(perm), vaddr)
    }
}

impl Page {
    /// When we obtain a PTE entry, we can convert it to a Page if it is
    /// not a leaf entry. Since we will consume the token pointing to the PTE,
    /// we guarantee that no one will be able to modify the PTE while we
    /// are using the Page.
    pub fn from_entry(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
    ) -> (r: (DekoPPtr<Page>, Tracked<DekoPointsTo<Page>>))
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            PageTableEntry::is_valid_pte_spec(perm),
        ensures
            r.1@.pptr() == r.0@,
            r.1@.mem_wf(),
            r.1@.wf(),
    {
        let vaddr = phys_to_virt(pte.borrow(Tracked(&perm)).address());

        unsafe {
            // I think we should add stronger precondition to
            // ensure that this is really 'safe'; this needs
            // 'transmute' functionality.
            DekoPPtr::<Page>::from_raw_uninit(vaddr.0)
        }
    }

    fn walk_level0(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            page@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            page.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        let idx = index_at_level::<0>(vaddr);
        let (entry, entry_perm) = unsafe {
            // ADD MORE
            DekoPPtr::<PageTableEntry>::from_raw_uninit((page.addr() + idx * 8) as u64)
        };

        assume(Mapping::Level0(entry, entry_perm).wf());
        Mapping::Level0(entry, entry_perm)
    }

    fn walk_level1(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            page@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            page.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        let idx = index_at_level::<1>(vaddr);
        let (entry, Tracked(entry_perm)) = unsafe {
            // ADD MORE
            DekoPPtr::<PageTableEntry>::from_raw_uninit((page.addr() + idx * 8) as u64)
        };

        assume(entry_perm.is_init());

        if PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
            let (next_page, next_perm) = Page::from_entry(entry, Tracked(entry_perm));
            Page::walk_level0(next_page, next_perm, vaddr)
        } else {
            Mapping::Level1(entry, Tracked(entry_perm))
        }
    }

    fn walk_level2(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            page@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            page.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        let idx = index_at_level::<2>(vaddr);
        let (entry, Tracked(entry_perm)) = unsafe {
            // ADD MORE
            DekoPPtr::<PageTableEntry>::from_raw_uninit((page.addr() + idx * 8) as u64)
        };

        assume(entry_perm.is_init());

        if PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
            let (next_page, next_perm) = Page::from_entry(entry, Tracked(entry_perm));
            Page::walk_level1(next_page, next_perm, vaddr)
        } else {
            Mapping::Level2(entry, Tracked(entry_perm))
        }
    }

    /// Walk the page now at the root level (level 3).
    fn walk_level3(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            page@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            page.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        let idx = index_at_level::<3>(vaddr);
        let (entry, Tracked(entry_perm)) = unsafe {
            // ADD MORE
            DekoPPtr::<PageTableEntry>::from_raw_uninit((page.addr() + idx * 8) as u64)
        };

        assume(entry_perm.is_init());

        if PageTableEntry::is_valid_pte(entry, Tracked(&entry_perm)) {
            let (next_page, next_perm) = Page::from_entry(entry, Tracked(entry_perm));
            Page::walk_level2(next_page, next_perm, vaddr)
        } else {
            Mapping::Level3(entry, Tracked(entry_perm))
        }
    }

    #[verifier::external_body]
    fn allocate_pte_level1(
        entry: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
        vaddr: VirtAddr,
        huge_page: bool,
    ) -> (r: Mapping)
        requires
            entry@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            entry.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
        if flags.contains(PRESENT) {
            return Mapping::Level3(entry, Tracked(perm));
        }
        let (page, Tracked(mut page_perm)) = {
            let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
            page.into_ptr(page_perm)
        };

        let flags = PRESENT | WRITABLE | USER | ACCESSED;
        let new_pte_value = make_private_address(page.addr() as u64) | flags;

        let tracked mut perm = perm;
        entry.write(Tracked(&mut perm), PageTableEntry(PhysAddr(new_pte_value)));

        let idx = index_at_level::<0>(vaddr);
        let next_entry = page.addr() + idx * 8;
        let (next_entry, Tracked(next_entry_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(next_entry as u64)
        };

        Mapping::Level0(next_entry, Tracked(next_entry_perm))
    }

    #[verifier::external_body]
    fn allocate_pte_level2(
        entry: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
        vaddr: VirtAddr,
        huge_page: bool,
    ) -> (r: Mapping)
        requires
            entry@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            entry.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
        if flags.contains(PRESENT) {
            return Mapping::Level3(entry, Tracked(perm));
        }
        let (page, Tracked(mut page_perm)) = {
            let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
            page.into_ptr(page_perm)
        };

        let flags = PRESENT | WRITABLE | USER | ACCESSED;
        let new_pte_value = make_private_address(page.addr() as u64) | flags;

        let tracked mut perm = perm;
        entry.write(Tracked(&mut perm), PageTableEntry(PhysAddr(new_pte_value)));

        let idx = index_at_level::<1>(vaddr);
        let next_entry = page.addr() + idx * 8;
        let (next_entry, Tracked(next_entry_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(next_entry as u64)
        };

        Page::allocate_pte_level1(next_entry, Tracked(next_entry_perm), vaddr, huge_page)
    }

    /// Allocates a page table entry at level 3 (the root level).
    #[verifier::external_body]
    fn allocate_pte_level3(
        entry: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
        vaddr: VirtAddr,
        huge_page: bool,
    ) -> (r: Mapping)
        requires
            entry@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            entry.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);
        if flags.contains(PRESENT) {
            return Mapping::Level3(entry, Tracked(perm));
        }
        let (page, Tracked(mut page_perm)) = {
            let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
            page.into_ptr(page_perm)
        };

        let flags = PRESENT | WRITABLE | USER | ACCESSED;
        let new_pte_value = make_private_address(page.addr() as u64) | flags;

        let tracked mut perm = perm;
        entry.write(Tracked(&mut perm), PageTableEntry(PhysAddr(new_pte_value)));

        let idx = index_at_level::<2>(vaddr);
        let next_entry = page.addr() + idx * 8;
        let (next_entry, Tracked(next_entry_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(next_entry as u64)
        };

        Page::allocate_pte_level2(next_entry, Tracked(next_entry_perm), vaddr, huge_page)
    }

    /// Allocates a 4KB page table entry for a given virtual address.
    pub fn alloc_pte_4k(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            pgtable@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            pgtable.addr() + 0x1000 <= usize::MAX,
        ensures
            r.wf(),
    {
        let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr);

        match mapping {
            Mapping::Level0(entry, entry_perm) => Mapping::Level0(entry, entry_perm),
            Mapping::Level1(entry, entry_perm) => Page::allocate_pte_level1(
                entry,
                entry_perm,
                vaddr,
                false,
            ),
            Mapping::Level2(entry, entry_perm) => Page::allocate_pte_level2(
                entry,
                entry_perm,
                vaddr,
                false,
            ),
            Mapping::Level3(entry, entry_perm) => Page::allocate_pte_level3(
                entry,
                entry_perm,
                vaddr,
                false,
            ),
        }
    }

    #[verifier::external_body]
    pub fn do_split_4k(
        entry: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<DekoPointsTo<PageTableEntry>>,
    )
        requires
            entry@ == perm.pptr(),
            perm.is_init(),
            perm.mem_wf(),
            perm.wf(),
            entry.addr() + 0x1000 <= usize::MAX,
    {
        let mut flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&perm)).0.0);

        if !flags.contains(HUGE) {
            vstd::vpanic!("not a huge page");
        }

        // Allocate a new page.
        let (page, Tracked(mut page_perm)) = {
            let (page, page_perm) = Box::<Page>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
            page.into_ptr(page_perm)
        };
        let paddr = page.addr() as u64;

        // Get the starting address of the 2M page.
        let addr_2m = entry.borrow(Tracked(&perm)).address().0 & 0x000f_ffff_fff0_0000;

        flags.remove(HUGE);

        // Now populate the new leaf PTE.
        let mut i = 0u64;
        while i < PAGE_TABLE_ENTRY as u64
            invariant
                i <= PAGE_TABLE_ENTRY,
        {
            // Split this huge page into 512 4K pages.
            let addr_4k = addr_2m + (i * PAGE_SIZE);
            let (e, Tracked(mut e_perm)) = unsafe {
                // ADD MORE
                DekoPPtr::<PageTableEntry>::from_raw_uninit(page.addr() as u64 + i * 8)
            };

            e.write(
                Tracked(&mut e_perm),
                PageTableEntry(PhysAddr(make_private_address(addr_4k) | flags.bits())),
            );

            i += 1;
        }

        // Finally, update the original PTE to point to the new page.
        entry.write(
            Tracked(&mut perm),
            PageTableEntry(PhysAddr(make_private_address(paddr) | flags.bits())),
        );
        flush_tlb();
    }

    pub fn split_4k(mapping: Mapping)
        requires
            mapping.wf(),
    {
        match mapping {
            Mapping::Level0(_, _) => {},
            Mapping::Level1(entry, entry_perm) => {
                Page::do_split_4k(entry, entry_perm);
            },
            _ => {
                vstd::vpanic!("unexpected mapping type");
            },
        }
    }

    /// Sets the shared state for a 4KB page.
    #[verifier::external_body]
    pub fn set_shared_4k(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
    ) {
        // Should return a Level 1 mapping due to huge page.
        let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr);
        PageTable::split_4k(mapping);

        // walk again to obtain the level 0 mapping.
        let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr);
        match mapping {
            Mapping::Level0(entry, entry_perm) => {
                let Tracked(mut entry_perm) = entry_perm;
                let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&entry_perm)).0.0);
                let addr = entry.borrow(Tracked(&entry_perm)).address();
                let addr = make_shared_address(addr.0);

                entry.write(
                    Tracked(&mut entry_perm),
                    PageTableEntry(PhysAddr(addr | flags.bits())),
                );
            },
            _ => {
                vstd::vpanic!("unexpected mapping type");
            },
        }

        flush_tlb();
    }

    /// Maps a single page at the given virtual address to the given physical address
    /// with the given flags.
    #[verifier::external_body]
    pub fn map_page_4k(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<DekoPointsTo<Page>>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
    ) {
        let mapping = Page::alloc_pte_4k(pgtable, Tracked(perm), vaddr);

        match mapping {
            Mapping::Level0(entry, entry_perm) => {
                let Tracked(mut entry_perm) = entry_perm;
                let new_pte_value = make_private_address(paddr.0) | flags.bits();

                entry.write(Tracked(&mut entry_perm), PageTableEntry(PhysAddr(new_pte_value)));
            },
            _ => {
                vstd::vpanic!("unexpected mapping type");
            },
        }
    }

    #[verifier::external_body]
    fn get_pte_address(vaddr: VirtAddr) -> VirtAddr {
        VirtAddr(PTE_BASE.0 + ((vaddr.0 & 0x0000_FFFF_FFFF_F000) >> 9))
    }

    #[verifier::external_body]
    pub fn virt_to_frame(vaddr: VirtAddr) -> PageFrame {
        // Calculate the virtual addresses of each level of the paging
        // hierarchy in the self-map.
        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        let (pml4e, Tracked(pml4e_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(pml4e_addr.0)
        };

        let pml4e_flags = PteFlags::from_bits_truncate(pml4e.borrow(Tracked(&pml4e_perm)).0.0);
        if !pml4e_flags.contains(PRESENT) {
            vstd::vpanic!("not present");
        }
        let (pdpe, Tracked(pdpe_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(pdpe_addr.0)
        };
        let pdpe_flags = PteFlags::from_bits_truncate(pdpe.borrow(Tracked(&pdpe_perm)).0.0);
        if !pdpe_flags.contains(PRESENT) {
            vstd::vpanic!("not present");
        }
        if pdpe_flags.contains(HUGE) {
            return PageFrame::Frame1G(
                PhysAddr(pdpe.borrow(Tracked(&pdpe_perm)).address().0 + (vaddr.0 & 0x001F_FFFF)),
            );
        }
        let (pde, Tracked(pde_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(pde_addr.0)
        };
        let pde_flags = PteFlags::from_bits_truncate(pde.borrow(Tracked(&pde_perm)).0.0);
        if !pde_flags.contains(PRESENT) {
            vstd::vpanic!("not present");
        }
        if pde_flags.contains(HUGE) {
            return PageFrame::Frame2M(
                PhysAddr(pde.borrow(Tracked(&pde_perm)).address().0 + (vaddr.0 & 0x000F_FFFF)),
            );
        }
        let (pte, Tracked(pte_perm)) = unsafe {
            DekoPPtr::<PageTableEntry>::from_raw_uninit(pte_addr.0)
        };
        let pte_flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&pte_perm)).0.0);
        if !pte_flags.contains(PRESENT) {
            vstd::vpanic!("not present");
        }
        PageFrame::Frame4K(
            PhysAddr(pte.borrow(Tracked(&pte_perm)).address().0 + (vaddr.0 & 0x0000_0FFF)),
        )
    }
}

#[verifier::external_body]
pub fn test_shared() {
    let (page_root, perm) = get_initial_pgtable();

    // After "walk"ing, we still do not see the confidentiality bit unset.
    Page::set_shared_4k(page_root, perm, VirtAddr::new(0x10000));

    let (pgtable, pgtable_perm) = get_initial_pgtable();
    let mapping = PageTable::walk(pgtable, pgtable_perm, VirtAddr::new(0x10000));

    let Mapping::Level0(entry, Tracked(entry_perm)) = mapping else {
        vstd::vpanic!("unexpected mapping type");
    };

    let raw = entry.borrow(Tracked(&entry_perm)).0.0;
    if raw & (1 << 51) != 0 {
        vstd::vpanic!("expected shared bit to be set");
    }
    let flags = PteFlags::from_bits_truncate(raw);
    if !flags.contains(PRESENT) {
        vstd::vpanic!("expected present bit to be set");
    }

    // Mapped to the wrong address???
    if entry.borrow(Tracked(&entry_perm)).address().0 != 0x10000 {
        vstd::vpanic!("unexpected address");
    }
}

#[verifier::external_body]
pub fn test_map() {
    let (test_ptr, Tracked(test_perm)) = {
        let (test_ptr, test_perm) = Box::<u64>::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
        test_ptr.into_ptr(test_perm)
    };
    test_ptr.write(Tracked(&mut test_perm), 0xdeadbeef);

    let vaddr = PERCPU_BASE;
    let paddr = PhysAddr(test_ptr.addr() as u64);
    let flags = PteFlags::data();
    let (pgtable, pgtable_perm) = get_initial_pgtable();

    Page::map_page_4k(pgtable, pgtable_perm, vaddr, paddr, flags);

    let (pgtable, pgtable_perm) = get_initial_pgtable();
    let mapping = PageTable::walk(pgtable, pgtable_perm, vaddr);

    if mapping.level() != 0 {
        vstd::vpanic!("unexpected mapping type");
    }
    let v = unsafe { *(vaddr.0 as *const u64) };

    if v != 0xdeadbeef {
        vstd::vpanic!("unexpected value");
    }
}

#[verifier::external_body]
#[inline(always)]
pub fn get_initial_pgtable() -> (r: (DekoPPtr<PageTable>, Tracked<DekoPointsTo<PageTable>>))
    ensures
        r.0@ === r.1@.pptr(),
        r.1.wf(),
        r.1@.wf_with_val(),
        r.1@.is_init(),
{
    unsafe {
        DekoPPtr::from_raw_uninit(
            (core::ptr::addr_of!(initial_page_table) as *const PageTable) as u64,
        )
    }
}

} // verus!
