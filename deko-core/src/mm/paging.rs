//! PGD (Page Global Directory)
//! PUD (Page Upper Directory)
//! PMD (Page Middle Directory)
//! PTE (Page Table Entry)
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::mm::{phys_to_virt, PTE_MASK_PRIVATE, PTE_MASK_SHARED};

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

extern "C" {
    /// This is the top-level, very initial page table that we can directly
    /// use to enable paging.
    #[link_name = "pgtable"]
    pub static mut pgtable: PageTable;
}

verus! {

deko_bitflags_quick! {
    Pte,
    data: { PRESENT, WRITABLE, USER, ACCESSED, DIRTY, HUGE, GLOBAL, NX },
}
// Note on the constants: Verus is having trouble verifying
// non-overflow/underflow of some arithmetic operations that
// involve constants and bit operations.
//
// We resort to hardcoding some of the results.


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
pub const PERCPU_BASE: VirtAddr = VirtAddr(0xFF0000000000);

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
pub const PTE_BASE: VirtAddr = VirtAddr(0xF68000000000);

//
// User-space mapping constants
//
/// Start of user memory address range
pub const USER_MEM_START: VirtAddr = VirtAddr(0);

/// End of user memory address range
pub const USER_MEM_END: VirtAddr = VirtAddr(USER_MEM_START.0 + (256 * SIZE_LEVEL3));

// marked as external_body because verus does not support complement.
#[inline(always)]
#[verifier::external_body]
fn strip_confidentiality_bits(paddr: u64) -> (r: u64) {
    paddr & !(PTE_MASK_PRIVATE.get().unwrap_or(&51))
}

// marked as external_body because verus does not support complement.
#[verifier::external_body]
#[inline(always)]
fn strip_shared_address_bits(paddr: u64) -> u64 {
    paddr & !(PTE_MASK_SHARED.get().unwrap())
}

/// Set address as private via mask.
#[verifier::external_body]
#[inline(always)]
fn make_private_address(paddr: u64) -> u64 {
    (strip_shared_address_bits(paddr) | PTE_MASK_PRIVATE.get().unwrap_or(&51))
}

/// Extract PML4 index (bits 47-39)
#[inline]
pub fn lvl3_index(addr: VirtAddr) -> (r: u64)
    requires
        addr.wf(),
    ensures
        r < 512,
        r == (addr@ >> 39) & 0x1ff,
{
    let r = (addr.0 >> 39) & 0x1ff;

    proof {
        let addr = addr@;

        assert(r < 512) by (bit_vector)
            requires
                (r == (addr >> 39) & 0x1ff),

    }

    r
}

#[inline]
pub fn lvl2_index(addr: VirtAddr) -> (r: u64)
    requires
        addr.wf(),
    ensures
        r < 512,
        r == (addr@ >> 30) & 0x1ff,
{
    let r = (addr.0 >> 30) & 0x1ff;

    proof {
        let addr = addr@;

        assert(r < 512) by (bit_vector)
            requires
                (r == (addr >> 30) & 0x1ff),

    }

    r
}

/// Extract PT index (bits 20-12)
#[inline]
pub fn lvl0_index(addr: VirtAddr) -> (r: u64)
    requires
        addr.wf(),
    ensures
        r < 512,
{
    let r = (addr.0 >> 12) & 0x1ff;

    proof {
        let addr = addr@;

        assert(r < 512) by (bit_vector)
            requires
                (r == (addr >> 12) & 0x1ff),

    }

    r
}

#[inline]
pub fn lvl1_index(addr: VirtAddr) -> (r: u64)
    requires
        addr.wf(),
    ensures
        r < 512,
        r == (addr@ >> 21) & 0x1ff,
{
    let r = (addr.0 >> 21) & 0x1ff;

    proof {
        let addr = addr@;

        assert(r < 512) by (bit_vector)
            requires
                (r == (addr >> 21) & 0x1ff),

    }

    r
}

/// Extract page offset (bits 11-0)
#[inline]
pub fn page_offset(addr: VirtAddr) -> (r: u64)
    requires
        addr.wf(),
    ensures
        r < 4096,
        r == addr@ & 0xfff,
{
    let r = addr.0 & 0xfff;

    proof {
        let addr = addr@;

        assert(r < 4096) by (bit_vector)
            requires
                (r == addr & 0xfff),

    }

    r
}

/// Get the index for a specific level
#[inline]
pub fn index_at_level(addr: VirtAddr, level: u8) -> (r: u64)
    requires
        addr.wf(),
        0 <= level <= 3,
    ensures
        r < 512,
{
    match level {
        3 => lvl3_index(addr),
        2 => lvl2_index(addr),
        1 => lvl1_index(addr),
        0 => lvl0_index(addr),
        _ => {
            proof {
                assert(false);
            }  // Unreachable

            vstd::vpanic!("11451419191810");
        },
    }
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

pub enum Mapping {
    Level3(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
    Level2(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
    Level1(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
    Level0(DekoPPtr<PageTableEntry>, Tracked<DekoPointsTo<PageTableEntry>>),
}

impl WellFormed for Mapping {
    open spec fn wf(&self) -> bool {
        let (ptr, perm) = match self {
            Mapping::Level3(p, perm) => (p, perm),
            Mapping::Level2(p, perm) => (p, perm),
            Mapping::Level1(p, perm) => (p, perm),
            Mapping::Level0(p, perm) => (p, perm),
        };

        &&& perm@.pptr() == ptr@
        &&& perm@.wf_with_val()
        &&& perm@.wf()
        &&& perm@.is_init()
    }
}

impl Mapping {
    pub open spec fn pptr(&self) -> &DekoPPtr<PageTableEntry> {
        match self {
            Mapping::Level3(p, _) => p,
            Mapping::Level2(p, _) => p,
            Mapping::Level1(p, _) => p,
            Mapping::Level0(p, _) => p,
        }
    }

    pub open spec fn lvl_spec(&self) -> u8 {
        match self {
            Mapping::Level3(..) => 3,
            Mapping::Level2(..) => 2,
            Mapping::Level1(..) => 1,
            Mapping::Level0(..) => 0,
        }
    }

    #[verifier::when_used_as_spec(lvl_spec)]
    pub fn lvl(&self) -> (r: u8)
        requires
            self.wf(),
        ensures
            r == self.lvl_spec(),
    {
        match self {
            Mapping::Level3(..) => 3,
            Mapping::Level2(..) => 2,
            Mapping::Level1(..) => 1,
            Mapping::Level0(..) => 0,
        }
    }

    pub fn from_page(
        pt: DekoPPtr<Page>,
        perm: Tracked<DekoPointsTo<Page>>,
        lvl: u8,
        idx: u64,
    ) -> (r: Self)
        requires
            pt@ == perm@.pptr(),
            perm@.wf_with_val(),
            perm@.is_init(),
            lvl == 3 || lvl == 2 || lvl == 1 || lvl == 0,
            idx < 512,
        ensures
            r.wf(),
            r.pptr()@ == perm@.value().0.idx_ptr(idx as int)@,
            r.lvl() == lvl,
    {
        let Tracked(mut perm) = perm;
        let mut pt = pt.take(Tracked(&mut perm));
        let (ptr, _) = pt.0.index_as_ptr(idx as usize);
        let tracked perm = pt.1.perms.borrow_mut().tracked_remove(idx as nat);

        match lvl {
            3 => Mapping::Level3(ptr, Tracked(perm)),
            2 => Mapping::Level2(ptr, Tracked(perm)),
            1 => Mapping::Level1(ptr, Tracked(perm)),
            0 => Mapping::Level0(ptr, Tracked(perm)),
            _ => {
                proof {
                    assert(false);
                }

                vstd::vpanic!("11451419191810");
            },
        }
    }

    pub fn raw(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self.pptr().addr(),
    {
        let r = match self {
            Mapping::Level3(p, _) => p.addr(),
            Mapping::Level2(p, _) => p.addr(),
            Mapping::Level1(p, _) => p.addr(),
            Mapping::Level0(p, _) => p.addr(),
        };

        r as _
    }

    #[verifier::external_body]
    pub fn write_pte(
        &self,
        paddr: PhysAddr,
        Tracked(perm): Tracked<&mut DekoPointsTo<PageTableEntry>>,
    )
        requires
            self.wf(),
            paddr.wf(),
            old(perm).wf(),
            old(perm).pptr() === self.pptr()@,
        ensures
            perm.wf(),
            perm.pptr() === self.pptr()@,
    {
        let addr = self.raw();

        unsafe {
            // This is safe because we know that
            // PageTableEntry is repr(C) and contains only a PhysAddr,
            // which is a u64 (repr(transparent)).
            *(addr as *mut u64) = paddr.0;
        }
    }
}

impl View for Mapping {
    type V = DekoPPtr<PageTableEntry>;

    open spec fn view(&self) -> DekoPPtr<PageTableEntry> {
        *self.pptr()
    }
}

/// An inner permission type used to track the storage and permissions
pub struct PageInner {
    pub storage: Ghost<Seq<DekoPPtr<PageTableEntry>>>,
    pub perms: Tracked<Map<nat, DekoPointsTo<PageTableEntry>>>,
}

impl PageInner {

}

impl WellFormed for PageInner {
    open spec fn wf(&self) -> bool {
        forall|i: nat|
            #![trigger self.perms@[i]]
            0 <= i < self.storage@.len() ==> {
                &&& self.perms@.dom().contains(i)
                &&& self.perms@[i].pptr() === self.storage@[i as int]@
                &&& self.perms@[i].wf()
                &&& self.perms@[i].wf_with_val()
                &&& self.perms@[i].is_init()
            }
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct PageFrameNumber(pub u64);

#[derive(Clone, Copy)]
#[repr(C)]
pub struct PageTableEntry(pub PhysAddr);

#[repr(C)]
#[allow(repr_transparent_external_private_fields)]
pub struct Page(pub Array<PageTableEntry, 512>, pub tracked PageInner);

#[repr(C)]
pub struct PageTable(pub Page);

impl PageFrameNumber {
    pub fn from_addr(paddr: PhysAddr) -> (r: Self)
        requires
            paddr.wf(),
        ensures
            r.wf(),
            r.0 == paddr@ >> 12,
    {
        PageFrameNumber(paddr.0 >> 12)
    }

    pub fn to_phys(self) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r@ == self.0 << 12,
    {
        PhysAddr(self.0 << 12)
    }
}

impl PageTableEntry {
    #[verifier::external_body]
    pub fn read_pte(vaddr: VirtAddr) -> (r: PageTableEntry)
        requires
            vaddr.wf(),
        ensures
            r.wf(),
    {
        unsafe { *(vaddr.0 as *const PageTableEntry) }
    }
}

impl WellFormed for PageFrameNumber {
    closed spec fn wf(&self) -> bool {
        self.0.wf()
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
    open spec fn wf(&self) -> bool {
        &&& self.0.wf()
        &&& self.1.wf()
        &&& self.0@.len() == 512
        &&& self.1.storage@.len() == self.0@.len()
        &&& forall|i: nat|
            #![auto]
            0 <= i < 512 ==> {
                &&& self.1.perms@.dom().contains(i)
                &&& self.0.idx_ptr(i as int)@ == self.1.perms@[i].pptr()
                &&& self.0.idx_perms(i as int) == self.1.perms@[i]
            }
    }
}

impl WellFormed for PageTable {
    closed spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

impl PageTableEntry {
    #[verifier::inline]
    pub open spec fn flags_spec(&self) -> Set<Pte> {
        from_bits(self.0@ & Pte_ALL_BITS)
    }

    #[inline]
    pub fn flags(&self) -> (r: PteFlags)
        requires
            self.wf(),
        ensures
            r.inv(),
            r@ == self.flags_spec(),
    {
        PteFlags::from_bits_truncate(self.0.0)
    }
}

impl Page {
    #[inline]
    pub fn is_present(
        entry: DekoPPtr<PageTableEntry>,
        perm: Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        requires
            perm@.wf_with_val(),
            perm@.pptr() === entry@,
            perm@.is_init(),
        ensures
            r == perm@.value().flags_spec().contains(Pte::PRESENT),
    {
        let pte = entry.borrow(perm);
        let flags = pte.flags();

        proof {
            PteFlags::lemma_each_bits_is_valid();
        }

        let b = flags.contains(PRESENT);

        proof {
            assert(flags.wf());
            assert(from_bits((PRESENT)) =~= set![Pte::PRESENT]) by {
                PteFlags::lemma_from_bits_single(Pte::PRESENT);
            }
            assert(b == from_bits(PRESENT).subset_of(flags@));
        }

        b
    }

    /// Converts a page table entry into a page frame number, if the entry is present.
    pub fn from_page_entry(
        entry: DekoPPtr<PageTableEntry>,
        perm: Tracked<DekoPointsTo<PageTableEntry>>,
    ) -> (r: (DekoPPtr<Self>, Tracked<DekoPointsTo<Self>>))
        requires
            perm@.value().flags_spec().contains(Pte::PRESENT),
            perm@.wf_with_val(),
            perm@.pptr() === entry@,
            perm@.is_init(),
        ensures
            r.1.wf(),
            r.1@.wf(),
            r.1@.pptr() === r.0@,
            r.1@.is_init(),
            r.1@.wf_with_val(),
    {
        let Tracked(mut perm) = perm;
        let pte = entry.take(Tracked(&mut perm));

        let addr = phys_to_virt(pte.0);

        unsafe {
            let (page, perm) = DekoPPtr::from_raw_uninit(addr.0);

            proof {
                // This is a hack; we need to have a way to verify this.
                assume(perm@.wf_with_val());
                assume(perm@.is_init());
            }

            (page, perm)
        }
    }
}

with_permission! {
    Page,
    parent: Ghost<PageTable>,
}

with_permission! {
    PageTable,
}

with_permission! {
    PageTableEntry,
    parent: Ghost<Page>,
}

impl PageTable {
    /// This function returns the root of the page table.
    ///
    /// The conversion is simple since `self` is just a wrapper around
    /// a `Page`; thus, if we have a pointer to `self`, we can
    /// directly return a pointer to the inner `Page`.
    ///
    /// This _consumes_ the page table's permission to avoid multiple
    /// owernships which can cause confusion.
    #[inline]
    pub fn root(page: DekoPPtr<Self>, Tracked(perm): Tracked<DekoPointsTo<Self>>) -> (r: (
        DekoPPtr<Page>,
        Tracked<DekoPointsTo<Page>>,
    ))
        requires
            perm.wf(),
            perm.pptr() === page@,
            perm.is_init(),
            perm.wf_with_val(),
        ensures
            r.1.wf(),
            r.1@.wf(),
            r.1@.pptr() === r.0@,
            r.1@.wf_with_val(),
            r.1@.is_init(),
    {
        unsafe { page.into(Tracked(perm)) }
    }

    /// Calculate the virtual address of a PTE in the self-map, which maps a
    /// specified virtual address.
    ///
    /// # Parameters
    /// - `vaddr': The virtual address whose PTE should be located.
    ///
    /// # Returns
    /// The virtual address of the PTE.
    fn get_pte_address(vaddr: VirtAddr) -> (r: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            r.wf(),
            r@ == PTE_BASE@ + ((vaddr@ & 0x0000_FFFF_FFFF_F000u64) >> 9),
    {
        let r = VirtAddr(PTE_BASE.0 + ((vaddr.0 & 0x0000_FFFF_FFFF_F000u64) >> 9));

        proof {
            assume(r.wf());
        }

        r
    }

    // TODO: Do we need to add flags here?
    pub fn virt_to_frame(vaddr: VirtAddr) -> (r: PageFrameNumber)
        requires
            vaddr.wf(),
        ensures
            r.wf(),
    {
        // Calculate the virtual addresses of each level of the paging
        // hierarchy in the self-map.
        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        // todo: we need to have a way for reasoning about
        // if these entries are `present`; we only allow
        // present entries to be looked up.
        let pml4e = PageTableEntry::read_pte(pml4e_addr);
        let pdpe = PageTableEntry::read_pte(pdpe_addr);
        let pde = PageTableEntry::read_pte(pde_addr);
        let pte = PageTableEntry::read_pte(pte_addr);

        // Check that all entries are present (pending).
        let paddr = pte.0.0 & 0x000f_ffff_ffff_f000;
        PageFrameNumber::from_addr(PhysAddr(strip_confidentiality_bits(paddr)))
    }

    fn walk(pt: DekoPPtr<Self>, vaddr: VirtAddr, perm: Tracked<DekoPointsTo<Self>>) -> (r: Mapping)
        requires
            vaddr.wf(),
            perm@.wf(),
            perm@.wf_with_val(),
            perm@.pptr() === pt@,
            perm@.is_init(),
        ensures
            r.wf(),
    // r.pptr() === PageTable::get_pte_address(vaddr)@,

    {
        let (root, root_perm) = PageTable::root(pt, perm);

        Self::walk_level3(root, vaddr, root_perm)
    }

    fn walk_leaf(pt: DekoPPtr<Page>, vaddr: VirtAddr, page_perm: Tracked<DekoPointsTo<Page>>) -> (r:
        Mapping)
        requires
            vaddr.wf(),
            page_perm@.wf_with_val(),
            page_perm@.pptr() === pt@,
            page_perm@.is_init(),
        ensures
            r.wf(),
    {
        let idx = index_at_level(vaddr, 0);

        Mapping::from_page(pt, page_perm, 0, idx)
    }

    fn walk_level1(
        pt: DekoPPtr<Page>,
        vaddr: VirtAddr,
        page_perm: Tracked<DekoPointsTo<Page>>,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            page_perm@.wf_with_val(),
            page_perm@.pptr() === pt@,
            page_perm@.is_init(),
        ensures
            r.wf(),
    {
        let Tracked(mut page_perm) = page_perm;
        let idx = index_at_level(vaddr, 1);

        let valid_entry = {
            let pt = pt.borrow(Tracked(&page_perm));
            let (entry, entry_perm) = pt.0.index_as_ptr(idx as usize);
            Page::is_present(entry, entry_perm)
        };

        if !valid_entry {
            return Mapping::from_page(pt, Tracked(page_perm), 1, idx);
        }

        let mut pt = pt.take(Tracked(&mut page_perm));
        let (entry, _) = pt.0.index_as_ptr(idx as usize);
        let tracked entry_perm = pt.1.perms.borrow_mut().tracked_remove(idx as nat);
        let (lv1_page, lv1_page_perm) = Page::from_page_entry(entry, Tracked(entry_perm));
        Self::walk_leaf(lv1_page, vaddr, lv1_page_perm)
    }

    fn walk_level2(
        pt: DekoPPtr<Page>,
        vaddr: VirtAddr,
        page_perm: Tracked<DekoPointsTo<Page>>,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            page_perm@.wf_with_val(),
            page_perm@.pptr() === pt@,
            page_perm@.is_init(),
        ensures
            r.wf(),
    {
        let Tracked(mut page_perm) = page_perm;
        let idx = index_at_level(vaddr, 2);

        let valid_entry = {
            let pt = pt.borrow(Tracked(&page_perm));
            let (entry, entry_perm) = pt.0.index_as_ptr(idx as usize);
            Page::is_present(entry, entry_perm)
        };

        if !valid_entry {
            return Mapping::from_page(pt, Tracked(page_perm), 2, idx);
        }

        let mut pt = pt.take(Tracked(&mut page_perm));
        let (entry, _) = pt.0.index_as_ptr(idx as usize);
        let tracked entry_perm = pt.1.perms.borrow_mut().tracked_remove(idx as nat);
        let (lv2_page, lv2_page_perm) = Page::from_page_entry(entry, Tracked(entry_perm));
        Self::walk_level1(lv2_page, vaddr, lv2_page_perm)
    }

    fn walk_level3(
        pt: DekoPPtr<Page>,
        vaddr: VirtAddr,
        page_perm: Tracked<DekoPointsTo<Page>>,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            page_perm@.wf_with_val(),
            page_perm@.pptr() === pt@,
            page_perm@.is_init(),
        ensures
            r.wf(),
    {
                let Tracked(mut page_perm) = page_perm;
        let idx = index_at_level(vaddr, 3);

        let valid_entry = {
            let pt = pt.borrow(Tracked(&page_perm));
            let (entry, entry_perm) = pt.0.index_as_ptr(idx as usize);
            Page::is_present(entry, entry_perm)
        };

        if !valid_entry {
            return Mapping::from_page(pt, Tracked(page_perm), 3, idx);
        }

        let mut pt = pt.take(Tracked(&mut page_perm));
        let (entry, _) = pt.0.index_as_ptr(idx as usize);
        let tracked entry_perm = pt.1.perms.borrow_mut().tracked_remove(idx as nat);
        let (lv3_page, lv3_page_perm) = Page::from_page_entry(entry, Tracked(entry_perm));
        Self::walk_level2(lv3_page, vaddr, lv3_page_perm)
    }

    #[verifier::external_body]
    fn from_mapping(m: &Mapping) -> (r: Tracked<DekoPointsTo<PageTableEntry>>)
        requires
            m.wf(),
        ensures
            r.wf(),
            r@.wf(),
            r@.pptr() === m.pptr()@,
    {
        let addr = m.raw();
        let (_, perm) = unsafe { DekoPPtr::from_raw_uninit(addr) };

        perm
    }

    fn allocate_pte(
        pt: DekoPPtr<Self>,
        Tracked(pt_perm): Tracked<DekoPointsTo<Self>>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            pt_perm.wf_with_val(),
            pt_perm.pptr() === pt@,
            pt_perm.is_init(),
        ensures
            pt_perm.wf(),
            pt_perm.pptr() === pt@,
            r.wf(),
            r.lvl() == 0,
    {
        let m = Self::walk(pt, vaddr, Tracked(pt_perm));

        match m {
            Mapping::Level0(..) => m,
            _ => {
                // ? recoverable?? or anything to enforce that this won't happen?
                vstd::vpanic!("unexpected mapping type");
            },
        }
    }

    pub fn map_page(
        pt: DekoPPtr<Self>,
        Tracked(pt_perm): Tracked<DekoPointsTo<Self>>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
    )
        requires
            vaddr.wf(),
            paddr.wf(),
            pt_perm.wf_with_val(),
            pt_perm.pptr() === pt@,
            pt_perm.is_init(),
        ensures
            pt_perm.wf(),
            pt_perm.pptr() === pt@,
    {
        let pte = Self::allocate_pte(pt, Tracked(pt_perm), vaddr);

        if pte.lvl() != 0 {
            assert(false);
        }

        match pte {
            Mapping::Level0(ptr, perm) => {
                let Tracked(mut perm) = perm;
                let paddr = ptr.borrow(Tracked(&perm)).0;
                let new_paddr = PhysAddr(strip_shared_address_bits(paddr.0) | flags.bits);
                
                let new_page_entry = PageTableEntry(new_paddr);
                ptr.write(Tracked(&mut perm), new_page_entry);
            },
            _ => {
                // ? recoverable?? or anything to enforce that this won't happen?
                vstd::vpanic!("unexpected mapping type");
            },
        }
    }
}

#[verusfmt::skip]
#[verifier::external_body]
#[inline(always)]
pub fn get_initial_pgtable() -> (r: (DekoPPtr<PageTable>, Tracked<DekoPointsTo<PageTable>>))
    ensures
        r.0@ === r.1@.pptr(),
        r.1.wf(),
        r.1@.wf_with_val(),
        r.1@.is_init(),
{
    unsafe { DekoPPtr::from_raw_uninit(&raw mut pgtable as *mut PageTable as u64) }
}

} // verus!
