// Re-export PTE_BASE from deko-std for backward compatibility
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
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
        r as int == index_at_level_spec(L as nat, vaddr),
{
    proof {
        assert forall|n: u64| n & 0x1ff < PAGE_TABLE_ENTRY by {
            bit_u64_and_auto();
        }
    }
    ((vaddr.0 >> (12 + L * 9)) & 0x1ff) as usize
}

/// A helper function to get the correct virtual address prefix for a given level.
pub open spec fn get_prefix_spec(level: nat, vaddr: VirtAddr) -> u64
    recommends
        level < 4,
{
    // level 3 (PML4) -> top 9 bits
    // level 2 (PDPT) -> top 18 bits
    // level 1 (PDT)  -> top 27 bits
    // level 0 (PT)   -> top 36 bits (the full VPN)
    let shift = 12 + (level + 1) * 9;
    vaddr@ >> shift
}

/// Specification version of index_at_level for use in specs
pub open spec fn index_at_level_spec(level: nat, vaddr: VirtAddr) -> int
    recommends
        level < 4,
{
    ((vaddr@ >> (12 + level * 9)) & 0x1ff) as int
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
    ctx: DekoPPtr<DekoCpuCtx>,
    Tracked(ctx_perm): Tracked<&DekoCpuCtxPermission>,
    paddr: PhysAddr,
) -> (r: VirtAddr)
    requires
        paddr.wf(),
        ctx_perm.wf_with(ctx),
        ctx_perm.pgtable_perm.mapping_space.physmap.in_range_spec(paddr)
            || ctx_perm.pgtable_perm.mapping_space.kernel.in_range_spec(paddr),
    ensures
        r.wf(),
        r == phys_to_virt_spec(ctx_perm.pgtable_perm.mapping_space, paddr),
{
    let ms = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).kernel_mapping();

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

/// The key used in our flattened page table storage map.
///
/// Here, the first element is the level (0 to 3), and the second element is the
/// upper bits of the virtual address used as the index in that level.
pub type PagePermissionIndex = (nat, u64);

///```text
///
///                                         ┌─────────────┐
///                                         │             │
///                                         │             ▼    this_page_perm
///                  ┌─────────────────┐    │    ┌─────────────────┐
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  │                 │    │    │                 │
///                  ├─────────────────┤    │    │                 │
///  parent_idx ────►│       PTE       ├────┘    │                 │
///                  ├─────────────────┤         │                 │
///                  │                 │         │                 │
///                  │                 │         │                 │
///                  └─────────────────┘         └─────────────────┘
///                         prev                         this
///```
pub tracked struct PagePermission {
    /// The level in the 4-level hierarchy (3=PML4, 2=PDPT, 1=PDT, 0=PT).
    pub level: nat,
    /// The index in the parent page at the given level to access this page.
    pub parent_index: int,
    /// The PTE value of this page in the _parent_ page.
    pub pte_perm: DekoPointsTo<PageTableEntry>,
    /// The permission to the page at this level.
    pub this_page_perm: DekoPointsTo<Page>,
}

/// This is the flattened page table where the key is (level, vpn_prefix) which
/// uniquely identifies a page table entry in the 4-level page table hierarchy;
/// the value stores is the next page permission.
type PageTableStorage = Map<PagePermissionIndex, PagePermission>;

with_permission! {
    PageTable,
    // the mapping space this page table belongs to =>
    // as sometimes we will need to convert between phys and virt addresses.
    mapping_space: MappingSpace,
    pgtable_perm: DekoPointsTo<PageTable>, // root permission.
    storage: PageTableStorage,
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
        let pdpe = pgtable_perm.storage[(3, get_prefix_spec(3, vaddr))];

        if pdpe.pte_perm.value().is_huge_pte_spec() {
            // 1GB huge page at level 3
            let base_addr = pdpe.pte_perm.value().address_spec(
                pgtable_perm.private_bit,
                pgtable_perm.shared_bit,
            );
            let offset = vaddr@ & 0x3FFF_FFFF;  // 30-bit offset for 1GB page
            PageFrame::Frame1G(PhysAddr((base_addr@ + offset) as u64))
        } else {
            let pdpte = pgtable_perm.storage[(2, get_prefix_spec(2, vaddr))];

            if pdpte.pte_perm.value().is_huge_pte_spec() {
                // 2MB huge page at level 2
                let base_addr = pdpte.pte_perm.value().address_spec(
                    pgtable_perm.private_bit,
                    pgtable_perm.shared_bit,
                );
                let offset = vaddr@ & 0x1F_FFFF;  // 21-bit offset for 2MB page
                PageFrame::Frame2M(PhysAddr((base_addr@ + offset) as u64))
            } else {
                let pde = pgtable_perm.storage[(1, get_prefix_spec(1, vaddr))];

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
                    let pte = pgtable_perm.storage[(0, get_prefix_spec(0, vaddr))];
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
        let vpn = get_prefix_spec(0, vaddr);
        let pte_perm = perm.storage[(0, vpn)].this_page_perm.value().0@.index(idx);
        let address = pte_perm.address_spec(perm.private_bit, perm.shared_bit);

        Mapping::Level0(
            DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
            Ghost((0, idx as u64)),
        )
    }

    pub open spec fn walk_addr_lvl1_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        let idx = index_at_level_spec(1, vaddr);
        let vpn = get_prefix_spec(1, vaddr);
        let pte = perm.storage[(1, vpn)].this_page_perm.value().0@.index(idx);

        if !pte.is_valid_pte_spec() {
            let address = pte.address_spec(private_bit, shared_bit);
            Mapping::Level1(
                DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
                Ghost((1, idx as u64)),
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
        let vpn = get_prefix_spec(2, vaddr);
        let pte_perm = perm.storage[(2, vpn)].this_page_perm.value().0@.index(idx);

        if !pte_perm.is_valid_pte_spec() {
            let address = pte_perm.address_spec(private_bit, shared_bit);
            Mapping::Level2(
                DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
                Ghost((2, idx as u64)),
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
        let vpn = get_prefix_spec(3, vaddr);
        let pte_perm = perm.storage[(3, vpn)].this_page_perm.value().0@.index(idx);

        if !pte_perm.is_valid_pte_spec() {
            let address = pte_perm.address_spec(private_bit, shared_bit);
            Mapping::Level3(
                DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
                Ghost((3, idx as u64)),
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
        Mapping::Level3(entry, idx)
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

    /// This function lifts a pointer to a page table entry into a page.
    #[inline]
    pub fn from_entry(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(pte_perm): Tracked<&DekoPointsTo<PageTableEntry>>,
        mapping_space: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: DekoPPtr<Page>)
        requires
            pte_perm.wf(),
            pte_perm.pptr() == pte@,
            pte_perm.is_init(),
            pte_perm.value().is_valid_pte_spec(),
            mapping_space.wf(),
            mapping_space.kernel.in_range_spec(
                pte_perm.value().address_spec(private_bit, shared_bit),
            ) || mapping_space.physmap.in_range_spec(
                pte_perm.value().address_spec(private_bit, shared_bit),
            ),
        ensures
            r.addr() == mapping_space.phys_to_virt_spec(
                pte_perm.value().address_spec(private_bit, shared_bit),
            )@ as usize,
    {
        let val = pte.borrow(Tracked(pte_perm));
        let paddr = val.address(private_bit, shared_bit);
        let vaddr = mapping_space.phys_to_virt(paddr);

        DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData))
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
            r == Self::allocate_pte_4k_lvl2_spec(
                entry,
                idx,
                vaddr,
                *old(pgtable_perm),
                *pgtable_perm,
                private_bit,
                shared_bit,
            ),
            pgtable_perm.wf_with_perm(),
    {
        // Place holder.
        Mapping::Level2(entry, idx)
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

    #[verifier::spinoff_prover]
    pub fn walk_addr_lvl0(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            ms.wf(),
            ms == perm.mapping_space,
            perm.wf_with_perm(),
            perm.page_pptr_has_perms(page, vaddr, 0),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl0_spec(*perm, vaddr),
    {
        let idx = index_at_level::<0>(vaddr);
        let ghost vpn = get_prefix_spec(0, vaddr);
        let tracked this_entry_perm = perm.storage.tracked_borrow((0, vpn));

        let entry = page.borrow(Tracked(&this_entry_perm.this_page_perm)).0.index(idx);
        let address = entry.address(private_bit, shared_bit);

        Mapping::Level0(
            DekoPPtr(vstd::simple_pptr::PPtr(address.0 as usize, core::marker::PhantomData)),
            Ghost((0, idx as u64)),
        )
    }

    pub fn walk_addr_lvl1(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            ms.wf(),
            ms == perm.mapping_space,
            perm.wf_with_perm(),
            perm.page_pptr_has_perms(page, vaddr, 1),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl1_spec(*perm, vaddr, private_bit, shared_bit),
    {
        let idx = index_at_level::<1>(vaddr);
        let ghost vpn = get_prefix_spec(1, vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((1, vpn)).this_page_perm;

        let (entry, entry_perm) = page.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, entry_perm) {
            let address = entry.borrow(entry_perm).address(private_bit, shared_bit);

            Mapping::Level1(
                DekoPPtr(
                    vstd::simple_pptr::PPtr(
                        #[verifier::truncate]
                        (address.0 as usize),
                        core::marker::PhantomData,
                    ),
                ),
                Ghost((1, idx as u64)),
            )
        } else {
            let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
            Page::walk_addr_lvl0(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        }
    }

    pub fn walk_addr_lvl2(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            ms.wf(),
            ms == perm.mapping_space,
            perm.wf_with_perm(),
            perm.page_pptr_has_perms(page, vaddr, 2),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl2_spec(*perm, vaddr, private_bit, shared_bit),
    {
        let idx = index_at_level::<2>(vaddr);
        let ghost vpn = get_prefix_spec(2, vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((2, vpn)).this_page_perm;

        let (entry, entry_perm) = page.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, entry_perm) {
            let address = entry.borrow(entry_perm).address(private_bit, shared_bit);
            Mapping::Level2(
                DekoPPtr(vstd::simple_pptr::PPtr(address.0 as usize, core::marker::PhantomData)),
                Ghost((2, idx as u64)),
            )
        } else {
            let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
            Page::walk_addr_lvl1(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        }
    }

    pub fn walk_addr_lvl3(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            ms.wf(),
            ms == perm.mapping_space,
            perm.wf_with_perm(),
            perm.page_pptr_has_perms(page, vaddr, 3),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl3_spec(*perm, vaddr, private_bit, shared_bit),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        let idx = index_at_level::<3>(vaddr);
        let ghost vpn = get_prefix_spec(3, vaddr);
        let tracked this_page_perm = &perm.storage.tracked_borrow((3, vpn)).this_page_perm;

        let (entry, entry_perm) = page.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, entry_perm) {
            let address = entry.borrow(entry_perm).address(private_bit, shared_bit);

            Mapping::Level3(
                DekoPPtr(vstd::simple_pptr::PPtr(address.0 as usize, core::marker::PhantomData)),
                Ghost((3, idx as u64)),
            )
        } else {
            let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
            Page::walk_addr_lvl2(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
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
            (3, get_prefix_spec(3, vaddr) as u64),
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
            (2, get_prefix_spec(2, vaddr) as u64),
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
            (1, get_prefix_spec(1, vaddr) as u64),
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
            (0, get_prefix_spec(0, vaddr) as u64),
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
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            vaddr.wf(),
            ms.wf(),
            ms == perm.mapping_space,
            perm.pgtable_perm.pptr().addr() == pgtable.addr(),
            perm.wf_with_perm(),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Self::walk_spec(*perm, vaddr, private_bit, shared_bit),
    {
        Self::walk_addr_lvl3(pgtable, Tracked(perm), vaddr, ms, private_bit, shared_bit)
    }

    /// Sets a given page as shared.
    pub fn set_shared_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    )
        requires
            vaddr.wf(),
            old(perm).pgtable_perm.pptr() == pgtable@,
            old(perm).wf_with_perm(),
            // perm.map_valid(vaddr, 0),
            old(perm).private_bit == private_bit,
            old(perm).shared_bit == shared_bit,
        ensures
            perm.wf_with_perm(),
            // Other fields do not change.
            old(perm).mapping_space == perm.mapping_space,
            old(perm).private_bit == perm.private_bit,
            old(perm).shared_bit == perm.shared_bit,
            perm.pgtable_perm.pptr() == pgtable@,
    {
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
    ///
    /// This function validates that all page table entries (PTEs) point to physical addresses
    /// that fall within the specified physical memory range [start_phys, end_phys).
    ///
    /// # Address Type Clarification
    /// - `pte.value().address_spec()` extracts the **physical address** from the PTE
    /// - This physical address is what gets checked against the range bounds
    ///
    /// # Parameters
    /// - `start_phys`: Lower bound of valid physical memory (inclusive)
    /// - `end_phys`: Upper bound of valid physical memory (exclusive)
    ///
    /// # Returns
    /// `true` if all present PTEs point to physical addresses within [start_phys, end_phys)
    pub open spec fn pte_within_range(&self, start_phys: u64, end_phys: u64) -> bool {
        &&& forall|i: (PagePermissionIndex, PagePermission)|
            #![auto]
            self.storage.contains_key(i.0) ==> {
                let pte = i.1.pte_perm;
                let paddr = pte.value().address_spec(self.private_bit, self.shared_bit);
                start_phys <= paddr@ < end_phys
            }
    }

    pub open spec fn page_pptr_has_perms(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        lvl: nat,
    ) -> bool {
        let vpn = get_prefix_spec(lvl, vaddr);

        &&& self.storage.contains_key((lvl, vpn))
        &&& {
            let entry = self.storage[(lvl, vpn)];

            &&& entry.this_page_perm.pptr() == page@
            &&& entry.this_page_perm.is_init()
            &&& entry.this_page_perm.wf()
            &&& entry.pte_perm.is_init()
            &&& entry.pte_perm.wf()
            &&& entry.pte_perm.value().is_valid_pte_spec()
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

    /// Get the virtual address of a page table entry for a given virtual address.
    pub open spec fn get_pte_address_spec(vaddr: VirtAddr) -> VirtAddr {
        let offset = (vaddr@ & 0x0000_FFFF_FFFF_F000u64) >> 9;
        VirtAddr((PTE_BASE@ + offset) as u64)
    }

    /// Helper: Check if an entry at a specific level is present and optionally huge
    pub open spec fn level_entry_valid(&self, vaddr: VirtAddr, level: nat, allow_huge: bool) -> bool
        recommends
            level <= 3,
    {
        let vpn = get_prefix_spec(level, vaddr);
        self.storage.contains_key((level, vpn)) && {
            let entry = self.storage[(level, vpn)];
            let pte = entry.pte_perm.value();
            pte.is_present_pte_spec() && (allow_huge || !pte.is_huge_pte_spec())
        }
    }

    /// Helper: Check if an entry at a specific level is a huge page
    pub open spec fn level_is_huge(&self, vaddr: VirtAddr, level: nat) -> bool
        recommends
            level <= 3,
    {
        let vpn = get_prefix_spec(level, vaddr);
        self.storage.contains_key((level, vpn)) && {
            let entry = self.storage[(level, vpn)];
            entry.pte_perm.value().is_huge_pte_spec()
        }
    }

    /// Checks if a virtual address has a valid mapping in the page table up to a specific level.
    ///
    /// This function uses the new VPN prefix-based approach to check if the virtual address
    /// has a valid translation path through the page table hierarchy.
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
        match level as u64 {
            3 => {
                // Check up to level 3 (PML4)
                self.level_entry_valid(vaddr, 3, true)
            },
            2 => {
                // Check up to level 2 (PDPT)
                self.level_entry_valid(vaddr, 3, true) && (self.level_is_huge(vaddr, 3)
                    || self.level_entry_valid(vaddr, 2, true))
            },
            1 => {
                // Check up to level 1 (PD)
                self.level_entry_valid(vaddr, 3, true) && (self.level_is_huge(vaddr, 3) || (
                self.level_entry_valid(vaddr, 2, true) && (self.level_is_huge(vaddr, 2)
                    || self.level_entry_valid(vaddr, 1, true))))
            },
            0 => {
                // Check complete translation path to level 0 (PT)
                self.level_entry_valid(vaddr, 3, true) && (self.level_is_huge(vaddr, 3) || (
                self.level_entry_valid(vaddr, 2, true) && (self.level_is_huge(vaddr, 2) || (
                self.level_entry_valid(vaddr, 1, true) && (self.level_is_huge(vaddr, 1)
                    || self.level_entry_valid(
                    vaddr,
                    0,
                    false,
                )  // Level 0 shouldn't be huge
                )))))
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

    /// This spec function says that the storage map (flattened map) should have
    /// a valid translation for every valid virtual address.
    pub open spec fn translates_all_valid_addresses(&self) -> bool {
        &&& forall|vaddr: VirtAddr, lvl: nat|
            #![trigger self.storage.contains_key((lvl, get_prefix_spec(lvl, vaddr)))]
            vaddr.wf() && 0 <= lvl <= 3 ==> {
                let prefix = get_prefix_spec(lvl, vaddr);
                self.storage.contains_key((lvl, prefix))
            }
    }

    /// **Unified VAddr-based Well-formedness**: Validates the entire page table through virtual address reasoning.
    ///
    /// This function ensures all requirements by validating that:
    /// 1. Every virtual address has corresponding translations at each level
    /// 2. For each vaddr's translation between level and level-1 (where level > 0), the translation makes sense
    ///
    /// This unified approach is more elegant and sufficient because it naturally covers:
    /// - Individual page well-formedness (through per-level validation)
    /// - Cross-level consistency (through level-to-level translation validation)
    /// - Physical address constraints (through address range checks)
    /// - Complete coverage (through universal quantification over all vaddrs)
    pub open spec fn vaddr_based_wf(&self) -> bool {
        forall|vaddr: VirtAddr, level: nat|
            #![trigger self.storage.contains_key((level, get_prefix_spec(level, vaddr)))]
            vaddr.wf() && 0 <= level <= 3 ==> {
                let vpn = get_prefix_spec(level, vaddr);

                // 1. Every vaddr has corresponding translation at each level
                self.storage.contains_key((level, vpn)) && {
                    let this_entry = self.storage[(level, vpn)];
                    let idx = index_at_level_spec(level, vaddr) as int;

                    // Basic well-formedness of this level's entry
                    &&& this_entry.wf()
                    &&& this_entry.level == level
                    &&& this_entry.parent_index == idx
                    &&& this_entry.this_page_perm.is_init() && this_entry.this_page_perm.wf()
                    &&& this_entry.pte_perm.is_init()
                        && this_entry.pte_perm.wf()
                    // Physical address constraints for this page
                    &&& this_entry.pte_perm.value().is_valid_pte_spec() ==> {
                        let page_paddr = this_entry.pte_perm.value().address_spec(
                            self.private_bit,
                            self.shared_bit,
                        );
                        self.mapping_space.kernel.in_range_spec(page_paddr)
                            || self.mapping_space.physmap.in_range_spec(page_paddr)
                    }
                    // 2. For level > 0, ensure translation between level and level-1 makes sense
                    &&& (level > 0 ==> {
                        let next_level = (level - 1) as nat;
                        let next_vpn = get_prefix_spec(next_level, vaddr);

                        self.storage.contains_key((next_level, next_vpn)) && {
                            let next_entry = self.storage[(next_level, next_vpn)];

                            // The PTE at this level should point to the next level's page
                            let entry = this_entry.this_page_perm.value().0@.index(
                                index_at_level_spec(level, vaddr) as int,
                            );

                            entry.is_valid_pte_spec() ==> {
                                let paddr = entry.address_spec(
                                    self.private_bit,
                                    self.shared_bit,
                                );

                                // Translation consistency: PTE should point to next level's page
                                &&& next_entry.pte_perm.value()@ == entry@
                                &&& (self.mapping_space.kernel.in_range_spec(paddr)
                                    || self.mapping_space.physmap.in_range_spec(paddr)) && {
                                    let expected_next_vaddr = self.mapping_space.phys_to_virt_spec(
                                        paddr,
                                    );

                                    &&& next_entry.this_page_perm.pptr().addr()
                                        == expected_next_vaddr@ as usize
                                }
                            }
                        }
                    })
                }
            }
    }

    /// **MASTER WELL-FORMEDNESS FUNCTION**
    ///
    /// This enforces the complete well-formedness of the entire page table permission structure
    /// using the unified virtual address-based approach.
    ///
    /// # Unified VAddr-based Approach
    ///
    /// This approach is elegant and sufficient because it validates:
    /// 1. **Every virtual address has corresponding translations at each level**
    /// 2. **For each vaddr's translation between level and level-1 (where level > 0), the translation makes sense**
    ///
    /// This naturally covers all requirements:
    /// - ✅ **Individual page well-formedness** (through per-level validation)
    /// - ✅ **Cross-level consistency** (through level-to-level translation validation)
    /// - ✅ **Physical address constraints** (through address range checks)
    /// - ✅ **Complete coverage** (through universal quantification over all vaddrs)
    ///
    /// # Verification Impact
    /// When this function returns `true`, you can be confident that:
    /// 1. 🛡️ **Memory Safety**: No access to invalid physical addresses
    /// 2. 🔗 **Structural Integrity**: Page table hierarchy is coherent
    /// 3. 📍 **Address Correctness**: All virtual↔physical mappings are valid
    /// 4. 🔐 **Permission Soundness**: All permission tokens are properly managed
    pub open spec fn wf_with_perm(&self) -> bool {
        // Basic well-formedness
        &&& self.pgtable_perm.is_init() && self.pgtable_perm.wf()
            && self.mapping_space.wf()
        // Unified virtual address-based validation
        &&& self.vaddr_based_wf()
        // Coverage: All valid addresses have translations
        &&& self.translates_all_valid_addresses()
    }
}

impl PagePermission {
    pub open spec fn wf_level(&self) -> bool {
        &&& self.level <= 3  // must be a valid level
        &&& 0 <= self.parent_index
            < PAGE_TABLE_ENTRY as int  // must be a valid index
        &&& self.pte_perm.is_init()
            && self.pte_perm.wf()  // must be initialized and well-formed
        &&& self.this_page_perm.is_init()
            && self.this_page_perm.wf()  // page permission must be valid

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
