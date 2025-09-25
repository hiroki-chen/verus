// Re-export PTE_BASE from deko-std for backward compatibility
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::DekoCpuCtx;
use crate::prelude::*;

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

verus! {

#[verifier::inline]
pub open spec fn strip_confidentiality_bits_spec(paddr: u64, private_bit: u64) -> u64 {
    paddr & !private_bit
}

#[verifier::inline]
pub open spec fn strip_shared_address_bits_spec(paddr: u64, shared_bit: u64) -> u64 {
    paddr & !shared_bit
}

#[verifier::inline]
pub open spec fn make_private_address_spec(paddr: u64, private_bit: u64, shared_bit: u64) -> u64 {
    strip_shared_address_bits_spec(paddr, shared_bit) | private_bit
}

#[verifier::inline]
pub open spec fn make_shared_address_spec(paddr: u64, private_bit: u64, shared_bit: u64) -> u64 {
    strip_confidentiality_bits_spec(paddr, private_bit) | shared_bit
}

#[verifier::when_used_as_spec(strip_confidentiality_bits_spec)]
pub fn strip_confidentiality_bits(paddr: u64, private_bit: u64) -> (r: u64)
    ensures
        r == strip_confidentiality_bits_spec(paddr, private_bit),
{
    paddr & !private_bit
}

#[verifier::when_used_as_spec(strip_shared_address_bits_spec)]
pub fn strip_shared_address_bits(paddr: u64, shared_bit: u64) -> (r: u64)
    ensures
        r == strip_shared_address_bits_spec(paddr, shared_bit),
{
    paddr & !shared_bit
}

#[verifier::when_used_as_spec(make_private_address_spec)]
pub fn make_private_address(paddr: u64, private_bit: u64, shared_bit: u64) -> (r: u64)
    ensures
        r == make_private_address_spec(paddr, private_bit, shared_bit),
{
    strip_shared_address_bits(paddr, shared_bit) | private_bit
}

#[verifier::when_used_as_spec(make_shared_address_spec)]
pub fn make_shared_address(paddr: u64, private_bit: u64, shared_bit: u64) -> (r: u64)
    ensures
        r == make_shared_address_spec(paddr, private_bit, shared_bit),
{
    strip_confidentiality_bits(paddr, private_bit) | shared_bit
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

/// Specification version of index_at_level for use in specs
pub open spec fn index_at_level_spec(level: nat, vaddr: VirtAddr) -> int
    recommends
        level < 4,
{
    ((vaddr.0 >> (12 + level * 9)) & 0x1ff) as int
}

pub open spec fn phys_to_virt_spec(ms: MappingSpace, paddr: PhysAddr) -> VirtAddr
    recommends
        ms.physmap.in_range_spec(paddr) || ms.kernel.in_range_spec(paddr),
{
    if ms.kernel.in_range_spec(paddr) {
        ms.kernel.phys_to_virt_spec(paddr)
    } else {
        ms.physmap.phys_to_virt_spec(paddr)
    }
}

/// Converts a physical address to a virtual address using the provided context's mapping space.
#[inline(always)]
pub fn phys_to_virt(
    ctx: DekoPPtr<DekoCtx>,
    Tracked(ctx_perm): Tracked<&DekoCtxPermission>,
    paddr: PhysAddr,
) -> (vaddr: VirtAddr)
    requires
        paddr.wf(),
        ctx_perm.wf_with(ctx),
        ctx_perm.in_heap_range(paddr),
    ensures
        vaddr.wf(),
        vaddr == phys_to_virt_spec(ctx_perm.mapping_space, paddr),
{
    let ms = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).mapping_space;

    ms.phys_to_virt(paddr)
}

deko_bitflags_quick! {
    Pte,
    data: { PRESENT, WRITABLE, USER, ACCESSED, DIRTY, GLOBAL, NX },
    writeable: { PRESENT, USER, WRITABLE, ACCESSED, DIRTY },
    read_only: { PRESENT, USER, ACCESSED },
    kernel_code: { PRESENT, GLOBAL },
}

/// Another wrapper over DekoPPtr for handling page tables.
///
/// Please be aware this is semantically _different_ from a `DekoPPtr<PageTableEntry>`;
/// casting between these two pointers require strict provenance and validity checks.
#[repr(C, align(8))]
pub struct DekoPagePtr(pub DekoPPtr<Page>);

/// A page table entry that is backed by a physical address.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct PageTableEntry(pub PhysAddr);

/// This struct contains a 4KiB array. Be careful when passing it around
/// as it might overflow the stack. The user should, at all times, pass
/// around a pointer to it instead of the struct itself.
#[repr(C)]
pub struct Page(pub Array<PageTableEntry, PAGE_TABLE_ENTRY>);

/// Used to index into the page table permission map [`PageTablePermission`].
/// (level, index)
pub type PagePermissionIndex = (nat, int);

///```text
///
///                                         ┌─────────────┐
///                                         │             │
///                   parent_page_perm      │             ▼    this_page_perm
///                  ┌─────────────────┐    │    ┌─────────────────┐
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  ├─────────────────┤    │    │                 │
///  this.idx   ────►│       PTE       ├────┘    │                 │
///                  ├─────────────────┤         │                 │
///                  │                 │         │                 │
///                  │                 │         │                 │
///                  └─────────────────┘         └─────────────────┘
///                         prev                        this
///```
pub tracked struct PagePermission {
    pub level: nat,  // 0, 1, 2, or 3 (PML4=3, PDPT=2, PD=1, PT=0)
    pub idx: int,    // the index used in the previous level page table
    pub value: DekoPPtr<PageTableEntry>,
    pub pte_perm: DekoPointsTo<PageTableEntry>,
    pub prev_page_perm: DekoPointsTo<Page>,
    pub this_page_perm: DekoPointsTo<Page>,
}

with_permission! {
    PageTable,
    // the mapping space this page table belongs to =>
    // as sometimes we will need to convert between phys and virt addresses.
    mapping_space: MappingSpace,
    pgtable_perm: DekoPointsTo<PageTable>, // root permission.
    storage: Map<PagePermissionIndex, PagePermission>,
    private_bit: u64,
    shared_bit: u64,
}

impl WellFormed for PageTablePermission {
    open spec fn wf(&self) -> bool {
        &&& self.pgtable_perm.is_init() && self.pgtable_perm.wf()
        &&& self.wf_with_perm()
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

impl View for PageTableEntry {
    type V = PhysAddr;

    #[verifier::inline]
    open spec fn view(&self) -> PhysAddr {
        self.0
    }
}

impl WellFormed for Page {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

impl View for Page {
    type V = PhysAddr;

    uninterp spec fn view(&self) -> Self::V;
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
    pub fn page_frame(&self, private_bit: u64) -> (r: PhysAddr) {
        let paddr = match *self {
            Self::Frame4K(pa) => pa,
            Self::Frame2M(pa) => pa,
            Self::Frame1G(pa) => pa,
        };
        PhysAddr(strip_confidentiality_bits(paddr.0, private_bit))
    }

    /// Get the address from the page frame, excluding the C/shared bit.
    pub fn address(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr) {
        PhysAddr(strip_shared_address_bits(self.page_frame(private_bit).0, shared_bit))
    }
}

impl Page {
    pub uninterp spec fn level(&self) -> nat;

    /// Specification functions for PageTable behavior
    pub open spec fn virt_to_frame_spec(
        vaddr: VirtAddr,
        private_bit: u64,
        pgtable_perm: PageTablePermission,
    ) -> (r: PageFrame)
        recommends
            pgtable_perm.map_valid(vaddr, 0),
    {
        let pte_index = index_at_level_spec(0, vaddr);
        let pde_index = index_at_level_spec(1, vaddr);
        let pdpte_index = index_at_level_spec(2, vaddr);
        let pml4e_index = index_at_level_spec(3, vaddr);

        // Walk through the page table hierarchy to find the final page frame
        let pdpe = pgtable_perm.storage[(3, pml4e_index as int)];

        if pdpe.pte_perm.value().is_huge_pte_spec() {
            // 1GB huge page at level 3
            let base_addr = pdpe.pte_perm.value().address_spec(
                pgtable_perm.private_bit,
                pgtable_perm.shared_bit,
            );
            let offset = vaddr@ & 0x3FFF_FFFF;  // 30-bit offset for 1GB page
            PageFrame::Frame1G(PhysAddr((base_addr@ + offset) as u64))
        } else {
            let pdpte = pgtable_perm.storage[(2, pdpte_index as int)];

            if pdpte.pte_perm.value().is_huge_pte_spec() {
                // 2MB huge page at level 2
                let base_addr = pdpte.pte_perm.value().address_spec(
                    pgtable_perm.private_bit,
                    pgtable_perm.shared_bit,
                );
                let offset = vaddr@ & 0x1F_FFFF;  // 21-bit offset for 2MB page
                PageFrame::Frame2M(PhysAddr((base_addr@ + offset) as u64))
            } else {
                let pde = pgtable_perm.storage[(1, pde_index as int)];

                if pde.pte_perm.value().is_huge_pte_spec() {
                    // 2MB huge page at level 1
                    let base_addr = pde.pte_perm.value().address_spec(
                        pgtable_perm.private_bit,
                        pgtable_perm.shared_bit,
                    );
                    let offset = vaddr@ & 0x1F_FFFF;  // 21-bit offset for 2MB page
                    PageFrame::Frame2M(PhysAddr((base_addr@ + offset) as u64))
                } else {
                    // 4KB page at level 0
                    let pte = pgtable_perm.storage[(0, pte_index as int)];
                    let base_addr = pte.pte_perm.value().address_spec(
                        pgtable_perm.private_bit,
                        pgtable_perm.shared_bit,
                    );
                    let offset = vaddr@ & 0xFFF;  // 12-bit offset for 4KB page
                    PageFrame::Frame4K(PhysAddr((base_addr@ + offset) as u64))
                }
            }
        }
    }

    pub open spec fn get_pte_address_spec(vaddr: VirtAddr) -> (r: VirtAddr) {
        let offset = (vaddr@ & 0x0000_FFFF_FFFF_F000u64) >> 9;
        VirtAddr((PTE_BASE@ + offset) as u64)
    }

    pub open spec fn allocate_pte_spec(
        mapping: Mapping,
        vaddr: VirtAddr,
        old_pgtable_perm: PageTablePermission,
        new_pgtable_perm: PageTablePermission,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        Self::allocate_pte_4k_spec(
            mapping,
            vaddr,
            old_pgtable_perm,
            new_pgtable_perm,
            private_bit,
            shared_bit,
        )
    }

    pub open spec fn walk_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping
        recommends
            perm.wf_with_perm(),
    {
        Self::walk_addr_lvl3_spec(perm, vaddr, private_bit, shared_bit)
    }

    pub open spec fn walk_addr_lvl0_spec(perm: PageTablePermission, vaddr: VirtAddr) -> Mapping
        recommends
            perm.wf_with_perm(),
    {
        let idx = index_at_level_spec(0, vaddr);
        let pte_perm = perm.storage[(0, idx as int)].pte_perm;

        Mapping::Level0(
            DekoPPtr(
                vstd::simple_pptr::PPtr(pte_perm.value()@@ as usize, core::marker::PhantomData),
            ),
            Ghost((0, idx)),
        )
    }

    pub open spec fn walk_addr_lvl1_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        let idx = index_at_level_spec(1, vaddr);
        let pte_perm = perm.storage[(1, idx as int)].pte_perm;

        let address = pte_perm.value().address_spec(private_bit, shared_bit);
        let paddr = perm.mapping_space.phys_to_virt_spec(address);

        if !pte_perm.value().is_valid_pte_spec() {
            Mapping::Level1(
                DekoPPtr(vstd::simple_pptr::PPtr(paddr@ as usize, core::marker::PhantomData)),
                Ghost((1, idx)),
            )
        } else {
            Page::walk_addr_lvl0_spec(perm, vaddr)
        }
    }

    pub open spec fn walk_addr_lvl2_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        let idx = index_at_level_spec(2, vaddr);
        let pte_perm = perm.storage[(2, idx as int)].pte_perm;

        let address = pte_perm.value().address_spec(private_bit, shared_bit);
        let paddr = perm.mapping_space.phys_to_virt_spec(address);

        if !pte_perm.value().is_valid_pte_spec() {
            Mapping::Level2(
                DekoPPtr(vstd::simple_pptr::PPtr(paddr@ as usize, core::marker::PhantomData)),
                Ghost((2, idx)),
            )
        } else {
            Page::walk_addr_lvl1_spec(perm, vaddr, private_bit, shared_bit)
        }
    }

    pub open spec fn walk_addr_lvl3_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        let idx = index_at_level_spec(3, vaddr);
        let pte_perm = perm.storage[(3, idx as int)].pte_perm;

        let address = pte_perm.value().address_spec(private_bit, shared_bit);
        let paddr = perm.mapping_space.phys_to_virt_spec(address);

        if !pte_perm.value().is_valid_pte_spec() {
            Mapping::Level3(
                DekoPPtr(vstd::simple_pptr::PPtr(paddr@ as usize, core::marker::PhantomData)),
                Ghost((3, idx)),
            )
        } else {
            Page::walk_addr_lvl2_spec(perm, vaddr, private_bit, shared_bit)
        }
    }

    pub open spec fn allocate_pte_4k_lvl1_spec(
        entry: DekoPPtr<PageTableEntry>,
        idx: Ghost<PagePermissionIndex>,
        vaddr: VirtAddr,
        old_pgtable_perm: PageTablePermission,
        new_pgtable_perm: PageTablePermission,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping
        recommends
            old_pgtable_perm.wf_with_perm(),
    {
        // Place holder.
        Mapping::Level1(entry, idx)
    }

    pub open spec fn allocate_pte_4k_lvl2_spec(
        entry: DekoPPtr<PageTableEntry>,
        idx: Ghost<PagePermissionIndex>,
        vaddr: VirtAddr,
        old_pgtable_perm: PageTablePermission,
        new_pgtable_perm: PageTablePermission,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping
        recommends
            old_pgtable_perm.wf_with_perm(),
    {
        // Place holder.
        Mapping::Level2(entry, idx)
    }

    pub open spec fn allocate_pte_4k_lvl3_spec(
        entry: DekoPPtr<PageTableEntry>,
        idx: Ghost<PagePermissionIndex>,
        vaddr: VirtAddr,
        old_pgtable_perm: PageTablePermission,
        new_pgtable_perm: PageTablePermission,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping
        recommends
            old_pgtable_perm.wf_with_perm(),
    {
        // Also must ensure that after this is called, the new_pgtable_perm
        // will have a present page for that.
        // Place holder.
        Mapping::Level1(entry, idx)
    }

    pub open spec fn allocate_pte_4k_spec(
        mapping: Mapping,
        vaddr: VirtAddr,
        old_pgtable_perm: PageTablePermission,
        new_pgtable_perm: PageTablePermission,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping
        recommends
            old_pgtable_perm.wf_with_perm(),
    {
        match mapping {
            Mapping::Level3(e, i) => Self::allocate_pte_4k_lvl3_spec(
                e,
                i,
                vaddr,
                old_pgtable_perm,
                new_pgtable_perm,
                private_bit,
                shared_bit,
            ),
            Mapping::Level2(e, i) => Self::allocate_pte_4k_lvl2_spec(
                e,
                i,
                vaddr,
                old_pgtable_perm,
                new_pgtable_perm,
                private_bit,
                shared_bit,
            ),
            Mapping::Level1(e, i) => Self::allocate_pte_4k_lvl1_spec(
                e,
                i,
                vaddr,
                old_pgtable_perm,
                new_pgtable_perm,
                private_bit,
                shared_bit,
            ),
            // No need to allocate anything.
            Mapping::Level0(e, i) => Mapping::Level0(e, i),
        }
    }

    pub fn allocate_pte_4k_lvl1(
        pgtable: DekoPPtr<PageTable>,
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        entry: DekoPPtr<PageTableEntry>,
        idx: Ghost<PagePermissionIndex>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            old(pgtable_perm).wf_with_perm(),
        ensures
            r.eq(
                &Self::allocate_pte_4k_lvl1_spec(
                    entry,
                    idx,
                    vaddr,
                    *old(pgtable_perm),
                    *pgtable_perm,
                    private_bit,
                    shared_bit,
                ),
            ),
            pgtable_perm.wf_with_perm(),
    {
        proof {}

        // Place holder.
        Mapping::Level1(entry, idx)
    }

    pub fn allocate_pte_4k_lvl2(
        pgtable: DekoPPtr<PageTable>,
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        entry: DekoPPtr<PageTableEntry>,
        idx: Ghost<PagePermissionIndex>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            old(pgtable_perm).wf_with_perm(),
        ensures
            r.eq(
                &Self::allocate_pte_4k_lvl2_spec(
                    entry,
                    idx,
                    vaddr,
                    *old(pgtable_perm),
                    *pgtable_perm,
                    private_bit,
                    shared_bit,
                ),
            ),
            pgtable_perm.wf_with_perm(),
    {
        // Place holder.
        Mapping::Level1(entry, idx)
    }

    pub fn allocate_pte_4k_lvl3(
        pgtable: DekoPPtr<PageTable>,
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        entry: DekoPPtr<PageTableEntry>,
        idx: Ghost<PagePermissionIndex>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            old(pgtable_perm).wf_with_perm(),
        ensures
            r.eq(
                &Self::allocate_pte_4k_lvl3_spec(
                    entry,
                    idx,
                    vaddr,
                    *old(pgtable_perm),
                    *pgtable_perm,
                    private_bit,
                    shared_bit,
                ),
            ),
            pgtable_perm.wf_with_perm(),
    {
        // Place holder.
        Mapping::Level3(entry, idx)
    }

    pub fn allocate_pte_4k(
        pgtable: DekoPPtr<PageTable>,
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        mapping: Mapping,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            mapping.wf(),
            vaddr.wf(),
            old(pgtable_perm).wf_with_perm(),
        ensures
            r.eq(
                &Self::allocate_pte_4k_spec(
                    mapping,
                    vaddr,
                    *old(pgtable_perm),
                    *pgtable_perm,
                    private_bit,
                    shared_bit,
                ),
            ),
            pgtable_perm.wf_with_perm(),
    {
        match mapping {
            Mapping::Level3(entry, idx) => {
                Page::allocate_pte_4k_lvl3(
                    pgtable,
                    Tracked(pgtable_perm),
                    entry,
                    idx,
                    vaddr,
                    private_bit,
                    shared_bit,
                )
            },
            Mapping::Level2(entry, idx) => {
                Page::allocate_pte_4k_lvl2(
                    pgtable,
                    Tracked(pgtable_perm),
                    entry,
                    idx,
                    vaddr,
                    private_bit,
                    shared_bit,
                )
            },
            Mapping::Level1(entry, idx) => {
                Page::allocate_pte_4k_lvl1(
                    pgtable,
                    Tracked(pgtable_perm),
                    entry,
                    idx,
                    vaddr,
                    private_bit,
                    shared_bit,
                )
            },
            // No need to allocate anything.
            Mapping::Level0(entry, idx) => Mapping::Level0(entry, idx),
        }
    }

    pub fn walk_addr_lvl0(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            perm.pgtable_perm.pptr() == pgtable@,
            perm.wf_with_perm(),
        ensures
            r.eq(&Page::walk_addr_lvl0_spec(*perm, vaddr)),
    {
        let idx = index_at_level::<0>(vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((0, idx as int)).this_page_perm;

        let entry = pgtable.borrow(Tracked(&this_page_perm)).0.index(idx);
        Mapping::Level0(
            DekoPPtr(vstd::simple_pptr::PPtr(entry.0.0 as usize, core::marker::PhantomData)),
            Ghost((0, idx as int)),
        )
    }

    pub fn walk_addr_lvl1(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            perm.pgtable_perm.pptr() == pgtable@,
            perm.wf_with_perm(),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r.eq(&Page::walk_addr_lvl1_spec(*perm, vaddr, private_bit, shared_bit)),
    {
        let idx = index_at_level::<1>(vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((1, idx as int)).this_page_perm;

        let (entry, entry_perm) = pgtable.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);
        let flag = PteFlags::from_bits_truncate(entry.borrow(entry_perm).0.0);

        if !flag.contains(PRESENT) {
            Mapping::Level1(
                DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData)),
                Ghost((1, idx as int)),
            )
        } else {
            let next_page = entry.cast_into::<Page>();
            Page::walk_addr_lvl0(next_page, Tracked(perm), vaddr)
        }
    }

    pub fn walk_addr_lvl2(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            perm.pgtable_perm.pptr() == pgtable@,
            perm.wf_with_perm(),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r.eq(&Page::walk_addr_lvl2_spec(*perm, vaddr, private_bit, shared_bit)),
    {
        let idx = index_at_level::<2>(vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((2, idx as int)).this_page_perm;

        let (entry, entry_perm) = pgtable.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);
        let flag = PteFlags::from_bits_truncate(entry.borrow(entry_perm).0.0);

        if !flag.contains(PRESENT) {
            Mapping::Level2(
                DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData)),
                Ghost((2, idx as int)),
            )
        } else {
            let next_page = entry.cast_into::<Page>();
            Page::walk_addr_lvl1(next_page, Tracked(perm), vaddr, private_bit, shared_bit)
        }
    }

    pub fn walk_addr_lvl3(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            perm.pgtable_perm.pptr() == pgtable@,
            perm.wf_with_perm(),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r.eq(&Page::walk_addr_lvl3_spec(*perm, vaddr, private_bit, shared_bit)),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let idx = index_at_level::<3>(vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((3, idx as int)).this_page_perm;

        let (entry, entry_perm) = pgtable.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);
        let flag = PteFlags::from_bits_truncate(entry.borrow(entry_perm).0.0);

        if !flag.contains(PRESENT) {
            Mapping::Level3(
                DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData)),
                Ghost((3, idx as int)),
            )
        } else {
            let next_page = entry.cast_into::<Page>();
            Page::walk_addr_lvl2(next_page, Tracked(perm), vaddr, private_bit, shared_bit)
        }
    }

    /// Get the virtual address of the page table entry for a given virtual address.
    #[verifier::when_used_as_spec(get_pte_address_spec)]
    #[inline]
    pub fn get_pte_address(vaddr: VirtAddr) -> (r: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            r.wf(),
            r == Self::get_pte_address_spec(vaddr),
    {
        proof {
            assert(vaddr.wf());

            let pte_base = PTE_BASE@;
            let vaddr = vaddr@;

            assert(vaddr & 0x0000_FFFF_FFFF_F000u64 <= 0x0000_FFFF_FFFF_F000u64) by {
                bit_u64_and_auto();
            };
            let shifted = (vaddr & 0x0000_FFFF_FFFF_F000u64) >> 9;
            assert(shifted <= 0x0000_007F_FFFF_FFE00u64) by (bit_vector)
                requires
                    shifted == (vaddr & 0x0000_FFFF_FFFF_F000u64) >> 9,
            ;
            vaddr & 0x0000_FFFF_FFFF_F000u64 <= 0x0000_FFFF_FFFF_F000u64;
        }

        VirtAddr(PTE_BASE.0 + ((vaddr.0 & 0x0000_FFFF_FFFF_F000) >> 9))
    }

    /// Allocates a new page table entry for the given virtual address at the appropriate level.
    #[inline]
    pub fn allocate_pte(
        pgtable: DekoPPtr<Self>,
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        mapping: Mapping,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            mapping.wf(),
            vaddr.wf(),
            old(pgtable_perm).wf_with_perm(),
        ensures
            r.eq(
                &Self::allocate_pte_spec(
                    mapping,
                    vaddr,
                    *old(pgtable_perm),
                    *pgtable_perm,
                    private_bit,
                    shared_bit,
                ),
            ),
            pgtable_perm.wf_with_perm(),
    {
        Self::allocate_pte_4k(
            pgtable,
            Tracked(pgtable_perm),
            mapping,
            vaddr,
            private_bit,
            shared_bit,
        )
    }

    /// Converts a virtual address to a page frame if it is mapped.
    pub fn virt_to_frame(
        vaddr: VirtAddr,
        private_bit: u64,
        Tracked(pgtable_perm): Tracked<&PageTablePermission>,
    ) -> (r: PageFrame)
        requires
            vaddr.wf(),
            pgtable_perm.wf_with_perm(),
            pgtable_perm.map_valid(vaddr, 0),
            private_bit == pgtable_perm.private_bit,
        ensures
            r.wf(),
            r == Self::virt_to_frame_spec(vaddr, private_bit, *pgtable_perm),
    {
        // Calculate the vaddr of each level.
        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        // We now read the PTEs at each level.
        let pml4e = PageTableEntry::read_pte(pml4e_addr, 3, Tracked(pgtable_perm));
        let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
            (3, index_at_level_spec(3, vaddr) as int),
        ).pte_perm;

        // Need to borrow it.
        let flags = PteFlags::from_bits_truncate(pml4e.borrow(Tracked(pte_perm)).0.0);
        if !flags.contains(PRESENT) {
            // Will not happen due to precondition there.
            proof {
                assert(false);
            }

            vstd::vpanic!("page not present");
        }
        let pdpe = PageTableEntry::read_pte(pdpe_addr, 2, Tracked(pgtable_perm));
        let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
            (2, index_at_level_spec(2, vaddr) as int),
        ).pte_perm;
        let flags = PteFlags::from_bits_truncate(pdpe.borrow(Tracked(pte_perm)).0.0);
        if !flags.contains(PRESENT) {
            // Will not happen due to precondition there.
            proof {
                assert(false);
            }
            vstd::vpanic!("page not present");
        }
        if flags.contains(HUGE) {
            // 1GB huge page at level 3
            let base_addr = pdpe.borrow(Tracked(pte_perm)).page_frame(private_bit);
            let offset = vaddr.0 & 0x3FFF_FFFF;  // 30-bit offset for 1GB page
            return PageFrame::Frame1G(PhysAddr((base_addr.0 + offset) as u64));
        }
        let pde = PageTableEntry::read_pte(pde_addr, 1, Tracked(pgtable_perm));
        let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
            (1, index_at_level_spec(1, vaddr) as int),
        ).pte_perm;
        let flags = PteFlags::from_bits_truncate(pde.borrow(Tracked(pte_perm)).0.0);
        if !flags.contains(PRESENT) {
            // Will not happen due to precondition there.
            proof {
                assert(false);
            }
            vstd::vpanic!("page not present");
        }
        if flags.contains(HUGE) {
            // 2MB huge page at level 2
            let base_addr = pde.borrow(Tracked(pte_perm)).page_frame(private_bit);
            let offset = vaddr.0 & 0x1F_FFFF;  // 21-bit offset for 2MB page
            return PageFrame::Frame2M(PhysAddr((base_addr.0 + offset) as u64));
        }
        let pte = PageTableEntry::read_pte(pte_addr, 0, Tracked(pgtable_perm));
        let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
            (0, index_at_level_spec(0, vaddr) as int),
        ).pte_perm;
        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(pte_perm)).0.0);
        if !flags.contains(PRESENT) {
            // Will not happen due to precondition there.
            proof {
                assert(false);
            }
            vstd::vpanic!("page not present");
        }
        let base_addr = pte.borrow(Tracked(pte_perm)).page_frame(private_bit);
        let offset = vaddr.0 & 0xFFF;  // 12-bit offset for 4KB page
        PageFrame::Frame4K(PhysAddr((base_addr.0 + offset) as u64))
    }

    /// Walks the page table to find the last valid page table entry for a given virtual address.
    #[inline]
    pub fn walk(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            perm.pgtable_perm.pptr().addr() == pgtable.addr(),
            perm.wf_with_perm(),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Self::walk_spec(*perm, vaddr, private_bit, shared_bit),
    {
        Self::walk_addr_lvl3(pgtable, Tracked(perm), vaddr, private_bit, shared_bit)
    }

    /// Sets a given page as shared.
    pub fn set_shared_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) {
        // // Should return a Level 1 mapping due to huge page.
        // let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr, private_bit, shared_bit);
        // PageTable::split_4k(mapping);
        // // walk again to obtain the level 0 mapping.
        // let mapping = PageTable::walk(pgtable, Tracked(perm), vaddr, private_bit, shared_bit);
        // match mapping {
        //     Mapping::Level0(entry, entry_perm) => {
        //         let Tracked(mut entry_perm) = entry_perm;
        //         let flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(&entry_perm)).0.0);
        //         let addr = entry.borrow(Tracked(&entry_perm)).address();
        //         let addr = make_shared_address(addr.0, private_bit, shared_bit);
        //         entry.write(
        //             Tracked(&mut entry_perm),
        //             PageTableEntry(PhysAddr(addr | flags.bits())),
        //         );
        //     },
        //     _ => {
        //         vstd::vpanic!("unexpected mapping type");
        //     },
        // }
        // flush_tlb();
    }

    /// Maps a single 4KB page at the given virtual address to the given physical address
    pub fn map_page_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    ) {
        vstd::vpanic!("implement me");
    }
}

impl PageTableEntry {
    /// Specification functions for PageTableEntry behavior
    pub open spec fn address_spec(&self, private_bit: u64, shared_bit: u64) -> PhysAddr {
        PhysAddr(
            strip_shared_address_bits_spec(
                strip_confidentiality_bits_spec(self.0.0 & 0x000f_ffff_ffff_f000, private_bit),
                shared_bit,
            ),
        )
    }

    pub open spec fn page_frame_spec(&self, private_bit: u64) -> PhysAddr {
        PhysAddr(strip_confidentiality_bits_spec(self.0.0 & 0x000f_ffff_ffff_f000, private_bit))
    }

    pub open spec fn is_valid_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0 & Pte_ALL_BITS);
        bits.contains(Pte::PRESENT) && !bits.contains(Pte::HUGE)
    }

    pub open spec fn is_huge_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0 & Pte_ALL_BITS);
        bits.contains(Pte::HUGE)
    }

    pub open spec fn is_present_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0 & Pte_ALL_BITS);  // bits = set.
        bits.contains(Pte::PRESENT)
    }

    /// Get the address from the page table entry, including the shared bit.
    #[inline]
    pub fn page_frame(&self, private_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.page_frame_spec(private_bit),
    {
        PhysAddr(strip_confidentiality_bits(self.0.0 & 0x000f_ffff_ffff_f000, private_bit))
    }

    /// Get the address from the page table entry, excluding the C/shared bit.
    #[verifier::when_used_as_spec(address_spec)]
    #[inline]
    pub fn address(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.address_spec(private_bit, shared_bit),
    {
        PhysAddr(strip_shared_address_bits(self.page_frame(private_bit).0, shared_bit))
    }

    /// This function checks whether a given PTE is valid in the sense that
    /// it is either not present, or it is huge page so that we will need to
    /// take extra care when handling it.
    pub fn is_valid_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r:
        bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_valid_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT) && !flags.contains(HUGE)
    }

    pub fn is_huge_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r:
        bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_huge_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(HUGE)
    }

    pub fn is_present_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r:
        bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_present_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT)
    }

    /// Reads the page table entry for a given virtual address from the page table.
    ///
    /// Note that the returned pointer is borrowed so reading/writing the PTE requires
    /// the caller with the appropriate permission.
    #[inline]
    pub fn read_pte(
        vaddr: VirtAddr,
        lvl: u64,
        Tracked(pgtable_perm): Tracked<&PageTablePermission>,
    ) -> (r: DekoPPtr<Self>)
        requires
            lvl <= 3,  // reading level 4 is meaningless.
            vaddr.wf(),
            pgtable_perm.wf_with_perm(),
            pgtable_perm.map_valid(vaddr, lvl as nat),
        ensures
            r.addr() == vaddr@ as usize,
    {
        DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData))
    }
}

impl PageTablePermission {
    /// Ensures all PTEs are within the valid physical range.
    pub open spec fn pte_within_range(&self, start_phys: u64, end_phys: u64) -> bool {
        &&& forall|i: (PagePermissionIndex, PagePermission)|
            #![auto]
            self.storage.contains_key(i.0) ==> {
                let pte = i.1.pte_perm;
                let paddr = pte.value().address_spec(self.private_bit, self.shared_bit);
                start_phys <= paddr@ < end_phys
            }
    }

    /// Updates the permission structure when a new page table entry is added
    /// This maintains the mirror property by ensuring the storage map reflects
    /// the actual page table structure
    pub open spec fn update_entry(&self, level: nat, idx: int, new_entry: PagePermission) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
            new_entry.level == level,
            new_entry.idx == idx,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            // If the key is already present from the map,
            // then its existing value is overwritten by the new value.
            storage: self.storage.insert((level, idx), new_entry),
            mapping_space: self.mapping_space,
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Removes an entry from the permission structure
    /// Used when a page table entry is deallocated or becomes invalid
    pub open spec fn remove_entry(&self, level: nat, idx: int) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.remove((level, idx)),
            mapping_space: self.mapping_space,
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Adds an entry to the permission structure only if it represents a present PTE
    /// This maintains the mirror property by only tracking present entries
    pub open spec fn add_present_entry(
        &self,
        level: nat,
        idx: int,
        new_entry: PagePermission,
    ) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
            new_entry.level == level,
            new_entry.idx == idx,
            new_entry.wf(),
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.insert((level, idx), new_entry),
            mapping_space: self.mapping_space,
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Removes an entry when it becomes non-present
    /// This maintains the mirror property by removing non-present entries
    pub open spec fn remove_non_present_entry(&self, level: nat, idx: int) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.remove((level, idx)),
            mapping_space: self.mapping_space,
            private_bit: self.private_bit,
            shared_bit: self.shared_bit,
        }
    }

    /// Updates an entry's presence status - adds if present, removes if not present
    pub open spec fn update_entry_presence(
        &self,
        level: nat,
        idx: int,
        new_entry: Option<PagePermission>,
    ) -> Self
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
            new_entry matches Some(entry) ==> (entry.level == level && entry.idx == idx
                && entry.wf()),
    {
        match new_entry {
            Some(entry) => self.add_present_entry(level, idx, entry),
            None => self.remove_non_present_entry(level, idx),
        }
    }

    /// Creates a new PageTablePermission with an empty storage map
    /// Used when initializing a new page table
    pub open spec fn empty(
        root_perm: DekoPointsTo<PageTable>,
        mapping_space: MappingSpace,
    ) -> Self {
        PageTablePermission {
            pgtable_perm: root_perm,
            storage: Map::empty(),
            mapping_space,
            private_bit: 0,
            shared_bit: 0,
        }
    }

    /// Validates that a page table modification preserves the mirror property
    /// Only allows updates for present entries
    pub open spec fn can_update_entry(
        &self,
        level: nat,
        idx: int,
        new_entry: PagePermission,
    ) -> bool
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        &&& new_entry.wf()
        &&& new_entry.level == level
        &&& new_entry.idx == idx
        // Entry must represent a present PTE
        &&& self.entry_is_present(
            level,
            idx,
            new_entry,
        )
        // Ensure the update maintains consistency with parent/child relationships
        &&& match level as u64 {
            4 => {
                // Root level - should point to initial page table (always present)
                new_entry.pte_perm.value().0@ == initial_page_table_value()
            },
            _ => {
                // For non-root levels, we no longer track next_page_perm
                // so we just ensure the entry is well-formed
                true
            },
        }
    }

    /// Validates that a page table entry can be removed (made non-present)
    pub open spec fn can_remove_entry(&self, level: nat, idx: int) -> bool
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        // Can only remove entries that are currently present in storage
        &&& self.storage.contains_key(
            (level, idx),
        )
        // Root entry (level 4, idx 0) should never be removed as it's always present
        &&& !(level == 4 && idx == 0)
    }

    /// Get the virtual address of a page table entry for a given virtual address.
    pub open spec fn get_pte_address_spec(vaddr: VirtAddr) -> VirtAddr {
        let offset = (vaddr@ & 0x0000_FFFF_FFFF_F000u64) >> 9;
        VirtAddr((PTE_BASE@ + offset) as u64)
    }

    /// Helper function to check if a level has a valid entry (present and optionally huge)
    pub open spec fn level_has_valid_entry(&self, level: nat, idx: int, allow_huge: bool) -> bool
        recommends
            0 <= level <= 3,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        &&& self.storage.contains_key((level, idx))
        &&& {
            let entry = self.storage[(level, idx)];
            entry.pte_perm.value().is_present_pte_spec() && (allow_huge
                || !entry.pte_perm.value().is_huge_pte_spec())
        }
    }

    /// Checks if a virtual address has a valid mapping in the page table up to a specific level.
    ///
    /// Unlike `pte_within_range` which checks the physical address in PTEs,
    /// this function checks if the virtual address has a valid translation path
    /// through the page table hierarchy tracked in this permission structure.
    ///
    /// The `level` parameter specifies the deepest level to check:
    /// - level 3: Check up to PML4 entries
    /// - level 2: Check up to PDPT entries  
    /// - level 1: Check up to PD entries
    /// - level 0: Check complete translation path to PT entries
    pub open spec fn map_valid(&self, vaddr: VirtAddr, level: nat) -> bool
        recommends
            vaddr.wf(),
            level <= 3,
    {
        let pte_index = index_at_level_spec(0, vaddr);
        let pde_index = index_at_level_spec(1, vaddr);
        let pdpte_index = index_at_level_spec(2, vaddr);
        let pml4e_index = index_at_level_spec(3, vaddr);

        // Check levels based on the requested depth
        match level as u64 {
            3 => {
                // Check up to level 3 (PML4)
                self.level_has_valid_entry(3, pml4e_index as int, true)
            },
            2 => {
                // Check up to level 2 (PDPT)
                &&& self.level_has_valid_entry(3, pml4e_index as int, true)
                &&& {
                    let pdpe = self.storage[(3, pml4e_index as int)];
                    pdpe.pte_perm.value().is_huge_pte_spec() || {
                        self.level_has_valid_entry(2, pdpte_index as int, true)
                    }
                }
            },
            1 => {
                // Check up to level 1 (PD)
                &&& self.level_has_valid_entry(3, pml4e_index as int, true)
                &&& {
                    let pdpe = self.storage[(3, pml4e_index as int)];
                    pdpe.pte_perm.value().is_huge_pte_spec() || {
                        &&& self.level_has_valid_entry(2, pdpte_index as int, true)
                        &&& {
                            let pdpte = self.storage[(2, pdpte_index as int)];
                            pdpte.pte_perm.value().is_huge_pte_spec() || {
                                self.level_has_valid_entry(1, pde_index as int, true)
                            }
                        }
                    }
                }
            },
            0 => {
                // Check complete translation path to level 0 (PT)
                &&& self.level_has_valid_entry(3, pml4e_index as int, true)
                &&& {
                    let pdpe = self.storage[(3, pml4e_index as int)];
                    pdpe.pte_perm.value().is_huge_pte_spec() || {
                        &&& self.level_has_valid_entry(2, pdpte_index as int, true)
                        &&& {
                            let pdpte = self.storage[(2, pdpte_index as int)];
                            pdpte.pte_perm.value().is_huge_pte_spec() || {
                                &&& self.level_has_valid_entry(1, pde_index as int, true)
                                &&& {
                                    let pde = self.storage[(1, pde_index as int)];
                                    pde.pte_perm.value().is_huge_pte_spec() || {
                                        self.level_has_valid_entry(0, pte_index as int, false)
                                    }
                                }
                            }
                        }
                    }
                }
            },
            _ => false  // Invalid level
            ,
        }
    }

    /// Helper function to check if an entry represents a present page table entry
    /// This checks that the PRESENT bit is set in the corresponding PTE
    pub open spec fn entry_is_present(&self, level: nat, idx: int, entry: PagePermission) -> bool
        recommends
            0 <= level <= 4,
            0 <= idx < PAGE_TABLE_ENTRY as int,
    {
        // Check the PRESENT bit in the PageTableEntry using the is_present_spec function
        entry.pte_perm.value().is_present_pte_spec()
    }

    /// Page table at level 3 does not have a parent page table entry
    /// So we only check that it points to itself.
    pub open spec fn point_to_self(&self, entry: PagePermission) -> bool {
        &&& entry.this_page_perm.pptr().addr() == entry.prev_page_perm.pptr().addr()
        &&& if entry.idx == PGTABLE_LVL3_IDX_PTE_SELFMAP as int {
            let expected_this_page_vaddr = self.mapping_space.phys_to_virt_spec(
                entry.prev_page_perm.value().0@.index(entry.idx).address_spec(
                    self.private_bit,
                    self.shared_bit,
                ),
            );
            entry.this_page_perm.pptr().addr() == expected_this_page_vaddr@ as usize
        } else {
            true
        }
    }

    /// Validates the address consistency in the page table hierarchy
    /// Ensures that virtual and physical address mappings are consistent:
    /// The PTE's virtual address matches: virt_to_phys(parent_page.addr + idx * 8) == pte_perm.addr
    pub open spec fn consistent_address_mappings(&self, entry: PagePermission) -> bool {
        let expected_this_page_vaddr = self.mapping_space.phys_to_virt_spec(
            entry.prev_page_perm.value().0@.index(entry.idx).address_spec(
                self.private_bit,
                self.shared_bit,
            ),
        );
        let expected_pte = entry.prev_page_perm.value().0@.index(entry.idx);

        &&& entry.this_page_perm.pptr().addr() == expected_this_page_vaddr@ as usize
        &&& entry.pte_perm.value() == expected_pte
    }

    // This specification says that for every entry in the storage map,
    // it must be well-formed and match its (level, index) key.
    // Only present entries are required to be in the storage map.
    //
    // This ensures the storage mirrors only the present entries in the actual page table structure.
    pub open spec fn wf_with_perm(&self) -> bool {
        // 1. Basic well-formedness
        &&& self.pgtable_perm.is_init()
            && self.pgtable_perm.wf()
        // 2. TODO: Root table exists and points to itself with initial value
        // 3. Page table should only contain valid levels (0, 1, 2, 3)
        &&& forall|key: PagePermissionIndex|
            self.storage.contains_key(key) ==> { 0 <= key.0 <= 3
            }
            // 4. Well-formedness at each level (0, 1, 2, 3)
        &&& forall|level: nat, idx: int|
            0 <= level <= 3 && 0 <= idx < PAGE_TABLE_ENTRY as int && self.storage.contains_key(
                (level, idx),
            ) ==> {
                let entry = self.storage[(level, idx)];
                &&& entry.wf()
                &&& entry.level == level
                &&& entry.idx == idx
                &&& entry.this_page_perm.is_init()
                // Entry must represent a present PTE
                &&& entry.pte_perm.value().is_present_pte_spec()
                // Value must be within the mapped region
                &&& self.mapping_space.kernel.in_range_spec(
                    entry.pte_perm.value().address_spec(self.private_bit, self.shared_bit),
                ) || self.mapping_space.physmap.in_range_spec(
                    entry.pte_perm.value().address_spec(self.private_bit, self.shared_bit),
                )
                &&& if level == 3 {
                    // 5. Root page table self-mapping
                    &&& self.point_to_self(entry)
                } else {
                    // 5. Consistent address mappings in page table hierarchy
                    &&& self.consistent_address_mappings(entry)
                }
            }
    }
}

impl PagePermission {
    pub open spec fn wf_level(&self) -> bool {
        &&& self.level <= 3  // must be a valid level
        &&& self.value@ == self.pte_perm.pptr()
        &&& self.prev_page_perm.is_init() && self.prev_page_perm.wf()
        &&& self.this_page_perm.is_init() && self.this_page_perm.wf()
    }
}

impl View for PageTablePermission {
    type V = Map<PagePermissionIndex, PagePermission>;

    closed spec fn view(&self) -> Self::V {
        self.storage
    }
}

impl WellFormed for PagePermission {
    open spec fn wf(&self) -> bool {
        &&& self.wf_level()
    }
}

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
/// Please note that the _wrapper_ pointer is the _virtual_address_ of the
/// corresponding PTEs at that level.
///
/// We don't define specs or proofs on this type because eventually
/// the reasoning is based on `PageTableEntry` and `PagePermissionIndex`.
pub enum Mapping {
    Level3(DekoPPtr<PageTableEntry>, Ghost<PagePermissionIndex>),
    Level2(DekoPPtr<PageTableEntry>, Ghost<PagePermissionIndex>),
    Level1(DekoPPtr<PageTableEntry>, Ghost<PagePermissionIndex>),
    Level0(DekoPPtr<PageTableEntry>, Ghost<PagePermissionIndex>),
}

// PageTableEntry can be safely cast into a Page when it represents a valid, present,
// non-huge page table entry that points to a properly aligned page table.
impl SafeCastInto<Page> for PageTableEntry {
    #[verifier::inline]
    open spec fn cast_valid(&self) -> bool {
        &&& self.wf()  // Well-formed
        &&& self.is_present_pte_spec()  // Must be present
        &&& !self.is_huge_pte_spec()  // Must not be a huge page (leaf entry)

    }

    uninterp spec fn cast_into(from: Self) -> Page;
}

// Auto implementation
impl WellFormed for Mapping {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        match self {
            Mapping::Level3(pte, idx) => idx@.0 == 3 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
            Mapping::Level2(pte, idx) => idx@.0 == 2 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
            Mapping::Level1(pte, idx) => idx@.0 == 1 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
            Mapping::Level0(pte, idx) => idx@.0 == 0 && 0 <= idx@.1 < PAGE_TABLE_ENTRY as int,
        }
    }
}

impl View for Mapping {
    type V = (DekoPPtr<PageTableEntry>, Ghost<PagePermissionIndex>);

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.into_inner_spec()
    }
}

impl Mapping {
    pub open spec fn into_inner_spec(&self) -> (
        DekoPPtr<PageTableEntry>,
        Ghost<PagePermissionIndex>,
    ) {
        match self {
            Mapping::Level3(pte, idx) => (*pte, *idx),
            Mapping::Level2(pte, idx) => (*pte, *idx),
            Mapping::Level1(pte, idx) => (*pte, *idx),
            Mapping::Level0(pte, idx) => (*pte, *idx),
        }
    }

    pub open spec fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Mapping::Level3(pte1, idx1), Mapping::Level3(pte2, idx2)) => pte1@ === pte2@ && idx1@
                == idx2@,
            (Mapping::Level2(pte1, idx1), Mapping::Level2(pte2, idx2)) => pte1@ === pte2@ && idx1@
                == idx2@,
            (Mapping::Level1(pte1, idx1), Mapping::Level1(pte2, idx2)) => pte1@ === pte2@ && idx1@
                == idx2@,
            (Mapping::Level0(pte1, idx1), Mapping::Level0(pte2, idx2)) => pte1@ === pte2@ && idx1@
                == idx2@,
            _ => false,
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

impl View for DekoPagePtr {
    type V = DekoPPtr<Page>;

    open spec fn view(&self) -> DekoPPtr<Page> {
        self.0
    }
}

impl DekoPagePtr {
    // /// Create a `DekoPagePtr` from a valid page table entry so we can access the
    // /// page table it points to. Note that since PTE contains the physical address
    // /// of the page table; to access the page table it points to, we need to convert
    // /// the physical address to a virtual address first.
    // pub closed spec fn from_pte_spec<T: PteBehavior>(
    //     pte: T,
    //     private_bit: u64,
    //     shared_bit: u64,
    // ) -> (r: Self) {
    //     let val = strip_shared_address_bits_spec(
    //         strip_confidentiality_bits_spec(pte@@ & 0x000f_ffff_ffff_f000, private_bit),
    //         shared_bit,
    //     );
    //     // TODO: Add phys to addr here.
    //     DekoPagePtr(DekoPPtr(vstd::simple_pptr::PPtr(val as usize, core::marker::PhantomData)))
    // }
    // /// Borrows a [`DekoPagePtr`] from a valid page table entry so we can access the
    // /// page table it points to. Note that since PTE contains the physical address
    // /// of the page table; to access the page table it points to, we need to convert
    // /// the physical address to a virtual address first.
    // #[inline]
    // pub fn from_pte(
    //     ctx: DekoPPtr<DekoCtx>,
    //     Tracked(ctx_perm): Tracked<&DekoCtxPermission>,
    //     pte: PageTableEntry,
    //     private_bit: u64,
    //     shared_bit: u64,
    // ) -> (r: Self)
    //     requires
    //         ctx_perm.wf_with(ctx),
    //         pte.wf(),
    //         pte.is_valid_pte_spec(),
    //     ensures
    //         r == Self::from_pte_spec(pte, private_bit, shared_bit),
    // {
    //     let paddr = pte.address(private_bit, shared_bit);
    //     DekoPagePtr(DekoPPtr(vstd::simple_pptr::PPtr(paddr.0 as usize, core::marker::PhantomData)))
    // }

}

} // verus!
