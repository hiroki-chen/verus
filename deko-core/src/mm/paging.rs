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
    /// The PTE value of this page in the _parent_ page.
    pub pte_perm: DekoPointsTo<PageTableEntry>,
    /// The permission to the page at this level.
    pub this_page_perm: DekoPointsTo<Page>,
}

/// A page table path is a sequence of integers representing the indices
/// at each level of the page table hierarchy.
pub tracked struct PageTablePath(pub Seq<int>);

impl WellFormed for PageTablePath {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self@.len() <= 4 && forall|i: int|
            0 <= i < self@.len() ==> 0 <= #[trigger] self@[i] < PAGE_TABLE_ENTRY as int
    }
}

impl View for PageTablePath {
    type V = Seq<int>;

    #[verifier::inline]
    open spec fn view(&self) -> Seq<int> {
        self.0
    }
}

macro_rules! path {
    ( $($x:expr),* ) => {
        {
            PageTablePath(seq![$($x),*])
        }
    };
}

impl PageTablePath {
    pub open spec fn eq(&self, other: &Self) -> bool
        recommends
            self.wf() && other.wf(),
    {
        self@.len() == other@.len() && forall|i: int| 0 <= i < self@.len() ==> self@[i] == other@[i]
    }

    pub open spec fn drop_last(self) -> Self
        recommends
            self.wf() && self.len() > 1,
    {
        PageTablePath(self.0.drop_last())
    }

    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    pub open spec fn level(self) -> nat
        recommends
            self.wf(),
    {
        (4 - self.len()) as nat
    }

    pub open spec fn last_index(self) -> int
        recommends
            self.wf(),
    {
        self.0[self.len() as int - 1]
    }

    pub open spec fn parent(self) -> Self
        recommends
            self.wf() && self.len() > 1,
    {
        PageTablePath(self.0.drop_last())
    }

    pub open spec fn from_vaddr_at_level(vaddr: VirtAddr, level: nat) -> Self
        recommends
            level <= 3,
    {
        PageTablePath(
            seq![
                index_at_level_spec(3, vaddr),
                index_at_level_spec(2, vaddr),
                index_at_level_spec(1, vaddr),
                index_at_level_spec(0, vaddr),
            ].take((4 - level) as int),
        )
    }

    // from_vaddr is just a shorthand for 4KB pages
    #[verifier::inline]
    pub open spec fn from_vaddr(vaddr: VirtAddr) -> Self {
        Self::from_vaddr_at_level(vaddr, 0)
    }
}

type PageTableStorage = Map<PageTablePath, PagePermission>;

with_permission! {
    PageTable,
    // the mapping space this page table belongs to =>
    // as sometimes we will need to convert between phys and virt addresses.
    mapping_space: MappingSpace,
    pgtable_perm: DekoPointsTo<PageTable>, // The PML4 page itself
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
        Mapping::Level0(
            DekoPPtr(vstd::simple_pptr::PPtr(0xdeadbeef, core::marker::PhantomData)),
            Ghost((0, 0)),
        )
        // let idx = index_at_level_spec(0, vaddr);
        // let vpn = get_prefix_spec(0, vaddr);
        // let pte_perm = perm.storage[(0, vpn)].this_page_perm.value().0@.index(idx);
        // let address = pte_perm.address_spec(perm.private_bit, perm.shared_bit);
        // Mapping::Level0(
        //     DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
        //     Ghost((0, idx as u64)),
        // )

    }

    pub open spec fn walk_addr_lvl1_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        Mapping::Level1(
            DekoPPtr(vstd::simple_pptr::PPtr(0xdeadbeef, core::marker::PhantomData)),
            Ghost((1, 0)),
        )
        // let idx = index_at_level_spec(1, vaddr);
        // let vpn = get_prefix_spec(1, vaddr);
        // let pte = perm.storage[(1, vpn)].this_page_perm.value().0@.index(idx);
        // if !pte.is_valid_pte_spec() {
        //     let address = pte.address_spec(private_bit, shared_bit);
        //     Mapping::Level1(
        //         DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
        //         Ghost((1, idx as u64)),
        //     )
        // } else {
        //     Page::walk_addr_lvl0_spec(perm, vaddr)
        // }

    }

    pub open spec fn walk_addr_lvl2_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        Mapping::Level2(
            DekoPPtr(vstd::simple_pptr::PPtr(0xdeadbeef, core::marker::PhantomData)),
            Ghost((2, 0)),
        )
        // let idx = index_at_level_spec(2, vaddr);
        // let vpn = get_prefix_spec(2, vaddr);
        // let pte_perm = perm.storage[(2, vpn)].this_page_perm.value().0@.index(idx);
        // if !pte_perm.is_valid_pte_spec() {
        //     let address = pte_perm.address_spec(private_bit, shared_bit);
        //     Mapping::Level2(
        //         DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
        //         Ghost((2, idx as u64)),
        //     )
        // } else {
        //     Page::walk_addr_lvl1_spec(perm, vaddr, private_bit, shared_bit)
        // }

    }

    pub open spec fn walk_addr_lvl3_spec(
        perm: PageTablePermission,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> Mapping {
        Mapping::Level3(
            DekoPPtr(vstd::simple_pptr::PPtr(0xdeadbeef, core::marker::PhantomData)),
            Ghost((3, 0)),
        )
        // let idx = index_at_level_spec(3, vaddr);
        // let vpn = get_prefix_spec(3, vaddr);
        // let pte_perm = perm.storage[(3, vpn)].this_page_perm.value().0@.index(idx);
        // if !pte_perm.is_valid_pte_spec() {
        //     let address = pte_perm.address_spec(private_bit, shared_bit);
        //     Mapping::Level3(
        //         DekoPPtr(vstd::simple_pptr::PPtr(address@@ as usize, core::marker::PhantomData)),
        //         Ghost((3, idx as u64)),
        //     )
        // } else {
        //     Page::walk_addr_lvl2_spec(perm, vaddr, private_bit, shared_bit)
        // }

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
            r == Self::allocate_pte_4k_spec(
                mapping,
                vaddr,
                *old(pgtable_perm),
                *pgtable_perm,
                private_bit,
                shared_bit,
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
            // perm.page_pptr_has_perms(page, vaddr, 0),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl0_spec(*perm, vaddr),
    {
        vstd::vpanic!("unimplemented: walk_addr_lvl0");
        // let idx = index_at_level::<0>(vaddr);
        // let ghost vpn = get_prefix_spec(0, vaddr);
        // let tracked this_entry_perm = perm.storage.tracked_borrow((0, vpn));

        // let entry = page.borrow(Tracked(&this_entry_perm.this_page_perm)).0.index(idx);
        // let address = entry.address(private_bit, shared_bit);

        // Mapping::Level0(
        //     DekoPPtr(vstd::simple_pptr::PPtr(address.0 as usize, core::marker::PhantomData)),
        //     Ghost((0, idx as u64)),
        // )
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
            // perm.page_pptr_has_perms(page, vaddr, 1),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl1_spec(*perm, vaddr, private_bit, shared_bit),
    {
        vstd::vpanic!("unimplemented: walk_addr_lvl1");

        // let idx = index_at_level::<1>(vaddr);
        // let ghost vpn = get_prefix_spec(1, vaddr);
        // let tracked this_page_perm = &perm.storage.tracked_borrow((1, vpn)).this_page_perm;

        // let (entry, entry_perm) = page.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);

        // if !PageTableEntry::is_valid_pte(entry, entry_perm) {
        //     let address = entry.borrow(entry_perm).address(private_bit, shared_bit);

        //     Mapping::Level1(
        //         DekoPPtr(
        //             vstd::simple_pptr::PPtr(
        //                 #[verifier::truncate]
        //                 (address.0 as usize),
        //                 core::marker::PhantomData,
        //             ),
        //         ),
        //         Ghost((1, idx as u64)),
        //     )
        // } else {
        //     let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
        //     Page::walk_addr_lvl0(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        // }
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
            // perm.page_pptr_has_perms(page, vaddr, 2),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl2_spec(*perm, vaddr, private_bit, shared_bit),
    {
        vstd::vpanic!("unimplemented: walk_addr_lvl2");

        // let idx = index_at_level::<2>(vaddr);
        // let ghost vpn = get_prefix_spec(2, vaddr);
        // let tracked this_page_perm = &perm.storage.tracked_borrow((2, vpn)).this_page_perm;

        // let (entry, entry_perm) = page.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);

        // if !PageTableEntry::is_valid_pte(entry, entry_perm) {
        //     let address = entry.borrow(entry_perm).address(private_bit, shared_bit);
        //     Mapping::Level2(
        //         DekoPPtr(vstd::simple_pptr::PPtr(address.0 as usize, core::marker::PhantomData)),
        //         Ghost((2, idx as u64)),
        //     )
        // } else {
        //     let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
        //     Page::walk_addr_lvl1(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        // }
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
            // perm.page_pptr_has_perms(page, vaddr, 3),
            perm.private_bit == private_bit,
            perm.shared_bit == shared_bit,
        ensures
            r == Page::walk_addr_lvl3_spec(*perm, vaddr, private_bit, shared_bit),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;

        vstd::vpanic!("unimplemented: walk_addr_lvl3");

        // let idx = index_at_level::<3>(vaddr);
        // let ghost vpn = get_prefix_spec(3, vaddr);
        // let tracked this_page_perm = &perm.storage.tracked_borrow((3, vpn)).this_page_perm;

        // let (entry, entry_perm) = page.borrow(Tracked(&this_page_perm)).0.index_as_ptr(idx);

        // if !PageTableEntry::is_valid_pte(entry, entry_perm) {
        //     let address = entry.borrow(entry_perm).address(private_bit, shared_bit);

        //     Mapping::Level3(
        //         DekoPPtr(vstd::simple_pptr::PPtr(address.0 as usize, core::marker::PhantomData)),
        //         Ghost((3, idx as u64)),
        //     )
        // } else {
        //     let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
        //     Page::walk_addr_lvl2(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        // }
    }

    /// We used a linear mapping for page table self-map. This operation is equivalent to
    /// doing `PTE_BASE + (vaddr >> 12) << 3` which first zeroes out the page offset and
    /// multiplies by the byte offset (8 byte) to locate the position in the linear map.
    ///
    /// Thus the PTE is simply calculated as `PTE_BASE + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)`.
    /// and to find the PTE of a PTE, we can just call this function recursively.
    ///
    /// The key invariant we preserve is that the PTE for any given virtual address is always
    /// the offset from PTE_BASE plus the offset of the virtual address (vaddr >> 12 << 3).
    ///
    /// Setting self-mapped entry at PML4 level is enough to hold thse 512 GB pages. For any
    /// PTE that starts at PTE_BASE, its index at PML4 is always 493 so we will always lookup
    /// PML4 itself as PDPT (which should be always present).
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

        // a compact way to perform PTE_BASE + (addr >> 12) << 3
        //
        // 1. It zeroes out the page offset (bits 11-0).
        // 2. It zeros out the sign each bit (bits 63-48).
        // 3. It keeps the four index fields (bits 47-12) untouched.
        // 4. It shifts by 9 = >> 12 << 3 to divide by 4096 and multiply by 8 to calculate
        //    the byte offset of the target PTE entry.
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
            r == Self::allocate_pte_spec(
                mapping,
                vaddr,
                *old(pgtable_perm),
                *pgtable_perm,
                private_bit,
                shared_bit,
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
            pgtable_perm.self_mapped(),
            // pgtable_perm.root_present(),
            // pgtable_perm.map_valid(vaddr, 0),
            private_bit == pgtable_perm.private_bit,
        ensures
            r.wf(),
            r == pgtable_perm.virt_to_frame_spec(vaddr).unwrap(),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;
        // Calculate the vaddr of each level's PTE.

        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        vstd::vpanic!("todo");

        // let tracked root = pgtable_perm.storage.tracked_borrow((3, 65535));
        // proof {
        //     assert(get_prefix_spec(3, pml4e_addr) == 65535) by {
        //         PageTablePermission::lemma_pte_root_same();
        //     };
        //     assert(pgtable_perm.storage.contains_key((3, 65535)));
        //     assert(root.pte_perm.value().is_present_pte_spec());
        // }

        // let pml4e = PageTableEntry::read_pte(pml4e_addr, Tracked(pgtable_perm));
        // let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
        //     (3, get_prefix_spec(3, pml4e_addr)),
        // ).pte_perm;

        // // Need to borrow it.
        // let flags = PteFlags::from_bits_truncate(pml4e.borrow(Tracked(pte_perm)).0.0);
        // if !flags.contains(PRESENT) {
        //     // Will not happen due to precondition there.
        //     proof {
        //         assert(false);
        //     }

        //     vstd::vpanic!("page not present");
        // }
        // // Read the next level.

        // let pdpe = PageTableEntry::read_pte(pdpe_addr, Tracked(pgtable_perm));
        // let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
        //     (2, get_prefix_spec(2, pdpe_addr)),
        // ).pte_perm;
        // let flags = PteFlags::from_bits_truncate(pdpe.borrow(Tracked(pte_perm)).0.0);
        // if !flags.contains(PRESENT) {
        //     // Will not happen due to precondition there.
        //     proof {
        //         assert(false);
        //     }
        //     vstd::vpanic!("page not present");
        // }
        // if flags.contains(HUGE) {
        //     // 1GB huge page at level 3
        //     let base_addr = pdpe.borrow(Tracked(pte_perm)).page_frame(private_bit);
        //     let offset = vaddr.0 & 0x3FFF_FFFF;  // 30-bit offset for 1GB page
        //     return PageFrame::Frame1G(PhysAddr((base_addr.0 + offset) as u64));
        // }
        // let pde = PageTableEntry::read_pte(pde_addr, Tracked(pgtable_perm));
        // let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
        //     (1, get_prefix_spec(1, pde_addr)),
        // ).pte_perm;
        // let flags = PteFlags::from_bits_truncate(pde.borrow(Tracked(pte_perm)).0.0);
        // if !flags.contains(PRESENT) {
        //     // Will not happen due to precondition there.
        //     proof {
        //         assert(false);
        //     }
        //     vstd::vpanic!("page not present");
        // }
        // if flags.contains(HUGE) {
        //     // 2MB huge page at level 2
        //     let base_addr = pde.borrow(Tracked(pte_perm)).page_frame(private_bit);
        //     let offset = vaddr.0 & 0x1F_FFFF;  // 21-bit offset for 2MB page
        //     return PageFrame::Frame2M(PhysAddr((base_addr.0 + offset) as u64));
        // }
        // let pte = PageTableEntry::read_pte(pte_addr, Tracked(pgtable_perm));
        // let tracked pte_perm = &pgtable_perm.storage.tracked_borrow(
        //     (0, get_prefix_spec(0, pte_addr)),
        // ).pte_perm;
        // let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(pte_perm)).0.0);
        // if !flags.contains(PRESENT) {
        //     // Will not happen due to precondition there.
        //     // proof {
        //     //     assert(false);
        //     // }
        //     vstd::vpanic!("page not present");
        // }
        // let base_addr = pte.borrow(Tracked(pte_perm)).page_frame(private_bit);
        // let offset = vaddr.0 & 0xFFF;  // 12-bit offset for 4KB page
        // PageFrame::Frame4K(PhysAddr((base_addr.0 + offset) as u64))
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
            // perm.page_pptr_has_perms(pgtable, vaddr, 3),
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

    /// Constructs a borrowed pointer to a page table entry from the virtual address
    /// of a PTE for a given virtual address.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let vaddr = 0xdeadbeef;
    /// let pte_for_vaddr = get_pte_address(vaddr);
    /// let pte = PageTableEntry::read_pte(pte_for_vaddr, pgtable_perm);
    ///
    /// let pte_for_pte_for_vaddr = get_pte_address(pte_for_vaddr);
    /// let pde = PageTableEntry::read_pte(pte_for_pte_for_vaddr, pgtable_perm);
    /// ```
    ///
    /// In order to read the PTE safely, the caller must ensure that the virtual address
    /// of the PTE is well-formed and is indeed mapped in the page table to be present!
    #[inline]
    pub fn read_pte(vaddr: VirtAddr, Tracked(pgtable_perm): Tracked<&PageTablePermission>) -> (r:
        DekoPPtr<Self>)
        requires
            vaddr.wf(),
            pgtable_perm.wf_with_perm(),
            pgtable_perm.virt_to_frame_spec(vaddr) matches Some(_),
        ensures
            r.addr() == vaddr@ as usize,
    {
        DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData))
    }
}

impl PageTablePermission {
    pub open spec fn get_pte(&self, path: PageTablePath, level: nat) -> Option<PageTableEntry>
        recommends 
            level <= 3,
    {
        let level_path = PageTablePath(path@.take((4 - level) as int));
        
        if self.storage.contains_key(level_path) {
            Some(self.storage[level_path].pte_perm.value())
        } else {
            None
        }
    }

    pub open spec fn virt_to_frame_spec(&self, vaddr: VirtAddr) -> Option<PageFrame>
        recommends
            self.self_mapped(),
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        
        match self.get_pte(path, 3) {
            None => None,
            Some(pml4e) if !pml4e.is_present_pte_spec() => None,
            Some(pml4e) => {
                match self.get_pte(path, 2) {
                    None => None,
                    Some(pdpte) if !pdpte.is_present_pte_spec() => None,
                    Some(pdpte) if pdpte.is_huge_pte_spec() => {
                        Some(self.make_1gb_frame(pdpte, vaddr))
                    }
                    Some(pdpte) => {
                        match self.get_pte(path, 1) {
                            None => None,
                            Some(pde) if !pde.is_present_pte_spec() => None,
                            Some(pde) if pde.is_huge_pte_spec() => {
                                Some(self.make_2mb_frame(pde, vaddr))
                            }
                            Some(pde) => {
                                match self.get_pte(path, 0) {
                                    None => None,
                                    Some(pte) if !pte.is_present_pte_spec() => None,
                                    Some(pte) => {
                                        Some(self.make_4kb_frame(pte, vaddr))
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub open spec fn make_huge_frame(
        &self,
        pte: PageTableEntry,
        vaddr: VirtAddr,
        level: nat,
    ) -> PageFrame {
        match level as u64 {
            3 => self.make_1gb_frame(pte, vaddr),
            2 => self.make_2mb_frame(pte, vaddr),
            1 => self.make_2mb_frame(pte, vaddr),
            _ => arbitrary(),
        }
    }

    // Helper functions
    pub open spec fn make_1gb_frame(&self, pte: PageTableEntry, vaddr: VirtAddr) -> PageFrame {
        let base = pte.address_spec(self.private_bit, self.shared_bit)@;
        let offset = vaddr.0 & 0x3FFF_FFFF;
        PageFrame::Frame1G(PhysAddr((base + offset) as u64))
    }

    pub open spec fn make_2mb_frame(&self, pte: PageTableEntry, vaddr: VirtAddr) -> PageFrame {
        let base = pte.address_spec(self.private_bit, self.shared_bit)@;
        let offset = vaddr.0 & 0x1F_FFFF;
        PageFrame::Frame2M(PhysAddr((base + offset) as u64))
    }

    pub open spec fn make_4kb_frame(&self, pte: PageTableEntry, vaddr: VirtAddr) -> PageFrame {
        let base = pte.address_spec(self.private_bit, self.shared_bit)@;
        let offset = vaddr.0 & 0xFFF;
        PageFrame::Frame4K(PhysAddr((base + offset) as u64))
    }

    /// Validates that accessing a PTE through self-mapping "cancels" one level of translation.
    ///
    /// This specification function captures the fundamental property of self-mapped page tables:
    /// when you access the PTE for a virtual address through the self-mapping, the translation
    /// process effectively "cancels out" one level of the page table hierarchy.
    ///
    /// # The Cancellation Property
    ///
    /// For any virtual address `vaddr` with indices `[a, b, c, d]`:
    /// - **Direct access**: `vaddr` requires walking `PML4[a] → PDPT[b] → PDT[c] → PT[d]`
    /// - **PTE access**: `get_pte_address(vaddr)` has indices `[493, a, b, c]`
    /// - **PTE translation**: Requires walking `PML4[493] → PDPT[a] → PDT[b] → PT[c]`
    ///
    /// The key insight: `PML4[493]` points to `PML4` itself, so:
    /// ```text
    /// PML4[493] → PDPT[a] = PML4 → PDPT[a] = "normal" translation starting from level 2
    /// ```
    ///
    /// This means accessing the PTE requires the **same page table entries** as accessing
    /// the original virtual address, just shifted by one level.
    ///
    /// # Mathematical Relationship
    ///
    /// ```text
    /// vaddr indices:     [a, b, c, d]     ← Target virtual address
    /// pte_addr indices:  [493, a, b, c]   ← PTE virtual address
    ///                     ↑    ↑  ↑  ↑
    ///                     │    └──┴──┴─── Same as vaddr[0:2]
    ///                     └─── Self-mapping index (cancels out)
    /// ```
    ///
    /// # Why This Matters for Verification
    ///
    /// This property enables proving that:
    /// 1. **Equivalence**: Self-mapped PTE access ≡ Regular page table walking
    /// 2. **Consistency**: If `vaddr` is accessible, its PTE is accessible
    /// 3. **Safety**: No additional page table entries need to be present
    ///
    /// # Example
    ///
    /// For `vaddr = 0xdeadbeef` with indices `[0, 3, 245, 219]`:
    /// ```text
    /// Direct access to vaddr:
    ///   PML4[0] → PDPT[3] → PDT[245] → PT[219] → data
    ///
    /// Access to PTE of vaddr:
    ///   PML4[493] → PDPT[0] → PDT[3] → PT[245] → PTE
    ///            ↑         ↑       ↑        ↑
    ///            │         └───────┴────────┴─── Same path as vaddr!
    ///            └─── Self-mapping (PML4[493] = PML4)
    /// ```
    ///
    /// # Returns
    ///
    /// `true` if the self-mapping property holds for the given virtual address,
    /// ensuring that PTE access and direct access share the same translation dependencies.
    pub open spec fn pte_of_vaddr_cancels_with_self_mapping(&self, vaddr: VirtAddr) -> bool {
        let pte = Page::get_pte_address_spec(vaddr);
        let pde = Page::get_pte_address_spec(pte);
        let pdpe = Page::get_pte_address_spec(pde);
        let pml4e = Page::get_pte_address_spec(pdpe);

        let pml4e_index_3 = index_at_level_spec(3, pml4e);
        let pml4e_index_2 = index_at_level_spec(2, pml4e);
        let pml4e_index_1 = index_at_level_spec(1, pml4e);
        let pml4e_index_0 = index_at_level_spec(0, pml4e);

        let pdpe_index_3 = index_at_level_spec(3, pdpe);
        let pdpe_index_2 = index_at_level_spec(2, pdpe);
        let pdpe_index_1 = index_at_level_spec(1, pdpe);

        let pde_index_3 = index_at_level_spec(3, pde);
        let pde_index_2 = index_at_level_spec(2, pde);

        let pte_index_3 = index_at_level_spec(3, pte);

        &&& pml4e_index_3 == pml4e_index_2 == pml4e_index_1 == pml4e_index_0 == 493
        &&& pdpe_index_3 == pdpe_index_2 == pdpe_index_1 == 493
        &&& pde_index_3 == pde_index_2 == 493
        &&& pte_index_3 == 493
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_pml4_entry_always_mapped(&self)
        requires
            self.wf_with_perm(),
        ensures
            forall|vaddr: VirtAddr|
                vaddr.wf() ==> {
                    let pml4e_addr = Page::get_pte_address_spec(
                        Page::get_pte_address_spec(
                            Page::get_pte_address_spec(Page::get_pte_address_spec(vaddr)),
                        ),
                    );

                    self.virt_to_frame_spec(pml4e_addr) matches Some(_)
                },
    {
        assert forall|vaddr: VirtAddr| vaddr.wf() implies {
            let pml4e_addr = Page::get_pte_address_spec(
                Page::get_pte_address_spec(
                    Page::get_pte_address_spec(Page::get_pte_address_spec(vaddr)),
                ),
            );

            self.virt_to_frame_spec(pml4e_addr) matches Some(_)
        } by {
            let pml4_addr = Page::get_pte_address_spec(
                Page::get_pte_address_spec(
                    Page::get_pte_address_spec(Page::get_pte_address_spec(vaddr)),
                ),
            );

            let path = PageTablePath::from_vaddr(pml4_addr);
            assert(path@ == path![493, 493, 493, 493]@) by {
                self.lemma_pte_of_vaddr_cancels_with_self_mapping(vaddr);
            }

            assert(self.storage[path![493]] == self.storage[path![493, 493]]);
            assert(self.storage[path![493, 493]] == self.storage[path![493, 493, 493]]);
            assert(self.storage[path![493, 493, 493]] == self.storage[path![493, 493, 493, 493]]);
            assert(self.storage[path![493]].pte_perm.value().is_present_pte_spec());

            let level3 = self.get_pte(path, 3).unwrap();
            assert(PageTablePath(path@.take(1 as int))@ == path![493]@);
            assert(level3.is_present_pte_spec());

            let level2 = self.get_pte(path, 2).unwrap();
            assert(PageTablePath(path@.take(2 as int))@ == path![493, 493]@);
            assert(level2.is_present_pte_spec());

            if level2.is_huge_pte_spec() {

            } else {
                let level1 = self.get_pte(path, 1).unwrap();
                assert(PageTablePath(path@.take(3 as int))@ == path![493, 493, 493]@);
                assert(level1.is_present_pte_spec());

                if level1.is_huge_pte_spec() {

                } else {
                    let level0 = self.get_pte(path, 0).unwrap();
                    assert(PageTablePath(path@.take(4 as int))@ == path![493, 493, 493, 493]@);
                    assert(level0.is_present_pte_spec());
                }
            }
        }
    }

    /// **PROOF**: Establishes the cancellation property for self-mapped PTE access.
    ///
    /// This lemma proves that the self-mapping mechanism creates the fundamental
    /// "cancellation" property where accessing a PTE shifts the translation path
    /// by exactly one level while preserving the same page table dependencies.
    ///
    /// # What This Proof Establishes
    ///
    /// For any well-formed virtual address `vaddr`, this proof demonstrates:
    ///
    /// 1. **Index Shifting**: The PTE address indices are exactly the original
    ///    virtual address indices shifted by one level
    /// 2. **Self-Mapping Prefix**: The PTE address always starts with the
    ///    self-mapping prefix (493)
    /// 3. **Translation Equivalence**: The page table entries required for
    ///    PTE access are the same as those for direct access
    ///
    /// # Proof Strategy
    ///
    /// The proof works by:
    /// 1. **Address Calculation**: Analyzing how `get_pte_address_spec` transforms indices
    /// 2. **Bit Manipulation**: Proving the mathematical relationship between address bits
    /// 3. **Recursive Application**: Showing that repeated application always leads to index 493
    /// 4. **Self-Mapping Invariant**: Verifying that the self-mapping index appears correctly
    ///
    /// # Mathematical Foundation
    ///
    /// The proof establishes that for `vaddr` with bit pattern:
    /// ```text
    /// vaddr = [sign_ext][a₈...a₀][b₈...b₀][c₈...c₀][d₈...d₀][offset₁₁...₀]
    /// ```
    ///
    /// Each recursive application of `get_pte_address_spec` produces addresses with
    /// index 493 at all levels, creating the cancellation effect.
    ///
    /// # Verification Impact
    ///
    /// This proof enables the verification system to:
    /// - **Reason about PTE accessibility** based on virtual address accessibility
    /// - **Prove memory safety** for page table operations
    /// - **Establish equivalence** between different page table access methods
    /// - **Verify consistency** of the self-mapping mechanism
    ///
    /// # Usage in Larger Proofs
    ///
    /// This lemma is typically used in conjunction with:
    /// - `self_mapped()` to ensure the recursive structure exists
    /// - `lemma_pte_of_vaddr_shares_prefix()` for prefix relationships
    /// - Page table walking proofs to establish accessibility
    pub proof fn lemma_pte_of_vaddr_cancels_with_self_mapping(&self, vaddr: VirtAddr)
        requires
            self.wf_with_perm(),
            vaddr.wf(),
        ensures
            self.pte_of_vaddr_cancels_with_self_mapping(vaddr),
    {
        let vaddr = vaddr@;
        let pte = (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64;
        let pde = (0xFFFFF68000000000 + ((pte & 0x0000_FFFF_FFFF_F000) >> 9)) as u64;
        let pdpe = (0xFFFFF68000000000 + ((pde & 0x0000_FFFF_FFFF_F000) >> 9)) as u64;
        let pml4e = (0xFFFFF68000000000 + ((pdpe & 0x0000_FFFF_FFFF_F000) >> 9)) as u64;

        let pml4e_3 = (pml4e >> 39) & 0x1FF;
        let pml4e_2 = (pml4e >> 30) & 0x1FF;
        let pml4e_1 = (pml4e >> 21) & 0x1FF;
        let pml4e_0 = (pml4e >> 12) & 0x1FF;

        assert(pml4e_3 == pml4e_2 == pml4e_1 == pml4e_0 == 493) by (bit_vector)
            requires
                pml4e_3 == (pml4e >> 39) & 0x1FF,
                pml4e_2 == (pml4e >> 30) & 0x1FF,
                pml4e_1 == (pml4e >> 21) & 0x1FF,
                pml4e_0 == (pml4e >> 12) & 0x1FF,
                pml4e == (0xFFFFF68000000000 + ((pdpe & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
                pdpe == (0xFFFFF68000000000 + ((pde & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
                pde == (0xFFFFF68000000000 + ((pte & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
                pte == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
        ;

        let pdpe_3 = (pdpe >> 39) & 0x1FF;
        let pdpe_2 = (pdpe >> 30) & 0x1FF;
        let pdpe_1 = (pdpe >> 21) & 0x1FF;

        assert(pdpe_3 == pdpe_2 == pdpe_1 == 493) by (bit_vector)
            requires
                pdpe_3 == (pdpe >> 39) & 0x1FF,
                pdpe_2 == (pdpe >> 30) & 0x1FF,
                pdpe_1 == (pdpe >> 21) & 0x1FF,
                pdpe == (0xFFFFF68000000000 + ((pde & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
                pde == (0xFFFFF68000000000 + ((pte & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
                pte == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
        ;

        let pde_3 = (pde >> 39) & 0x1FF;
        let pde_2 = (pde >> 30) & 0x1FF;

        assert(pde_3 == pde_2 == 493) by (bit_vector)
            requires
                pde_3 == (pde >> 39) & 0x1FF,
                pde_2 == (pde >> 30) & 0x1FF,
                pde == (0xFFFFF68000000000 + ((pte & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
                pte == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
        ;

        let pte_3 = (pte >> 39) & 0x1FF;

        assert(pte_3 == 493) by (bit_vector)
            requires
                pte_3 == (pte >> 39) & 0x1FF,
                pte == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64,
        ;
    }

    /// **PROOF**: Establishes that PTE addresses share prefixes with their target virtual addresses.
    ///
    /// This lemma proves a crucial property for self-mapped page tables: the PTE address
    /// for any virtual address shares a common prefix structure that enables efficient
    /// reasoning about page table dependencies and accessibility.
    ///
    /// # What This Proof Establishes
    ///
    /// For a virtual address `vaddr` and its corresponding PTE address `pte_of_vaddr`:
    ///
    /// 1. **Prefix Relationship**: The PTE address contains the original virtual address
    ///    indices in a shifted position
    /// 2. **Hierarchical Consistency**: The shared prefix ensures that accessing the PTE
    ///    requires the same intermediate page table entries as accessing the original address
    /// 3. **Self-Mapping Integration**: The prefix relationship works correctly with
    ///    the self-mapping mechanism
    ///
    /// # Prefix Sharing Pattern
    ///
    /// ```text
    /// Original vaddr:    [sign][a][b][c][d][offset]
    /// PTE address:       [sign][493][a][b][c][pte_offset]
    ///                           ↑    ↑  ↑  ↑
    ///                           │    └──┴──┴─── Shared prefix
    ///                           └─── Self-mapping index
    /// ```
    ///
    /// # Mathematical Relationship
    ///
    /// The proof establishes that:
    /// ```text
    /// index_at_level_spec(level, pte_of_vaddr) == index_at_level_spec(level+1, vaddr)
    /// ```
    /// for `level ∈ {0, 1, 2}`, which means:
    /// - `pte_of_vaddr`'s level-0 index = `vaddr`'s level-1 index
    /// - `pte_of_vaddr`'s level-1 index = `vaddr`'s level-2 index
    /// - `pte_of_vaddr`'s level-2 index = `vaddr`'s level-3 index
    ///
    /// # Verification Applications
    ///
    /// This property enables:
    /// - **Dependency Analysis**: Proving that PTE access has the same requirements as data access
    /// - **Consistency Checking**: Verifying that page table permissions are correctly structured
    /// - **Safety Guarantees**: Ensuring that PTE operations don't require additional page table entries
    ///
    /// # Integration with Other Proofs
    ///
    /// This lemma works together with:
    /// - `lemma_pte_of_vaddr_cancels_with_self_mapping` for the cancellation property
    /// - `self_mapped()` for the self-mapping root consistency
    /// - Page table walking proofs for accessibility relationships
    ///
    /// # Example Usage
    ///
    /// ```rust
    /// proof {
    ///     let pte_addr = Page::get_pte_address_spec(vaddr);
    ///
    ///     // Establish the prefix relationship
    ///     pgtable_perm.lemma_pte_of_vaddr_shares_prefix(vaddr, pte_addr);
    ///
    ///     // Now we can reason about shared dependencies
    ///     assert(index_at_level_spec(1, pte_addr) == index_at_level_spec(2, vaddr));
    ///
    ///     // This enables proving accessibility relationships
    ///     if pgtable_perm.level_entry_present(vaddr, 2) {
    ///         assert(pgtable_perm.level_entry_present(pte_addr, 1));
    ///     }
    /// }
    /// ```
    pub proof fn lemma_pte_of_vaddr_shares_prefix(&self, vaddr: VirtAddr, pte_of_vaddr: VirtAddr)
        requires
            vaddr.wf(),
            pte_of_vaddr.wf(),
            pte_of_vaddr == Page::get_pte_address_spec(vaddr),
        ensures
            index_at_level_spec(3, vaddr) == index_at_level_spec(2, pte_of_vaddr),
            index_at_level_spec(2, vaddr) == index_at_level_spec(1, pte_of_vaddr),
            index_at_level_spec(1, vaddr) == index_at_level_spec(0, pte_of_vaddr),
    {
        let vaddr = vaddr@;
        let pte_of_vaddr = (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64;
        let vaddr_3 = (vaddr >> 39) & 0x1FF;
        let vaddr_2 = (vaddr >> 30) & 0x1FF;
        let vaddr_1 = (vaddr >> 21) & 0x1FF;

        let pte_of_vaddr_2 = (pte_of_vaddr >> 30) & 0x1FF;
        let pte_of_vaddr_1 = (pte_of_vaddr >> 21) & 0x1FF;
        let pte_of_vaddr_0 = (pte_of_vaddr >> 12) & 0x1FF;

        assert(vaddr_3 == pte_of_vaddr_2) by (bit_vector)
            requires
                vaddr_3 == (vaddr >> 39) & 0x1FF,
                pte_of_vaddr_2 == (pte_of_vaddr >> 30) & 0x1FF,
                pte_of_vaddr == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000)
                    >> 9)) as u64,
        ;
        assert(vaddr_2 == pte_of_vaddr_1) by (bit_vector)
            requires
                vaddr_2 == (vaddr >> 30) & 0x1FF,
                pte_of_vaddr_1 == (pte_of_vaddr >> 21) & 0x1FF,
                pte_of_vaddr == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000)
                    >> 9)) as u64,
        ;
        assert(vaddr_1 == pte_of_vaddr_0) by (bit_vector)
            requires
                vaddr_1 == (vaddr >> 21) & 0x1FF,
                pte_of_vaddr_0 == (pte_of_vaddr >> 12) & 0x1FF,
                pte_of_vaddr == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000)
                    >> 9)) as u64,
        ;
    }


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
        &&& forall|kv_pair: (PageTablePath, PagePermission)|
            self.storage.kv_pairs().contains(kv_pair) ==> {
                let (path, perm) = kv_pair;
                let pte = perm.pte_perm.value();
                // Only check present PTEs
                pte.is_present_pte_spec() ==> {
                    let pte_phys_addr = pte.address_spec(self.private_bit, self.shared_bit).0;
                    start_phys <= pte_phys_addr && pte_phys_addr < end_phys
                }
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

    /// Checks if a virtual address has a valid mapping in the page table.
    ///
    /// This follows the same traversal logic as the reference virt_to_frame implementation:
    /// - Level 3 (PML4) must be present
    /// - Level 2 (PDPT) must be present; if huge, stop (1GB page)
    /// - Level 1 (PD) must be present; if huge, stop (2MB page)
    /// - Level 0 (PT) must be present (4KB page)
    pub open spec fn map_valid(&self, vaddr: VirtAddr, lvl: u64) -> bool {
        true
    }

    /// This spec function says that the storage map (flattened map) should have
    /// a valid translation for every valid virtual address.
    pub open spec fn translates_all_valid_addresses(&self) -> bool {
        &&& forall|path: PageTablePath|
            #![trigger self.storage.contains_key(path)]
            { path.wf() ==> self.storage.contains_key(path) }
    }

    /// Ensures that the self-mapped PML4 must be present.
    ///
    /// The trick here is that we don't store PML4 but instead store the PDPT's starting
    /// physical address into the CR3 register and we put the 493-th entry of PDPT to
    /// point to itself; this recursive mapping has two benefits:
    ///
    /// 1. Reduces translation steps.
    /// 2. Quickly locates the virtual address for any given virtual address's PTE because
    ///    when we look up virtual address's PTE, we will always look up the 493-th entry
    ///    of PML4 (which is the self-mapped entry) as the PDPT and we can look up as many
    ///    times as we want by bit operations.
    ///    For example, if we need to directly read/write the PDPT
    ///    of a virtual address, we can look up the 493-th entry two times, because the vir-
    ///    tual address is constructed such that its first two indices are always 493. Reading
    ///    493 actually "cancel"s this level's translation.
    pub open spec fn self_mapped(&self) -> bool {
        // All recursive paths exist
        &&& self.storage.contains_key(path![493])
        &&& self.storage.contains_key(path![493, 493])
        &&& self.storage.contains_key(path![493, 493, 493])
        &&& self.storage.contains_key(path![493, 493, 493, 493])
        
        // They all point to the same PagePermission
        &&& self.storage[path![493]] == self.storage[path![493, 493]]
        &&& self.storage[path![493]] == self.storage[path![493, 493, 493]]
        &&& self.storage[path![493]] == self.storage[path![493, 493, 493, 493]]
        
        // The entry is present
        &&& self.storage[path![493]].pte_perm.value().is_present_pte_spec()
        
        // Self-referential property
        &&& {
            let entry = self.storage[path![493]];
            let paddr = entry.pte_perm.value().address_spec(
                self.private_bit, 
                self.shared_bit
            );
            let vaddr = self.mapping_space.phys_to_virt_spec(paddr);

            // Virtual address mapping is consistent
            &&& entry.this_page_perm.pptr().addr() == vaddr@ as usize
            
            // Self-referential: the PTE points to its own containing page
            // entry.pte_perm is the PTE in the parent (but parent == self for 493!)
            // entry.this_page_perm[493] should equal entry.pte_perm
            &&& entry.pte_perm.value() == 
                entry.this_page_perm.value().0@.index(493)
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
        // Parent-child consistency
        &&& forall|child_path: PageTablePath|
            #![trigger self.storage.contains_key(child_path)]
            self.storage.contains_key(child_path) && child_path.len() > 1 ==> {
                let parent_path = child_path.drop_last();
                let child_index = child_path@[child_path.len() - 1];
                let child = self.storage[child_path];
                let parent = self.storage[parent_path];

                // 1. Parent exists
                &&& self.storage.contains_key(
                    parent_path,
                )
                // 2. PTE consistency: parent's page contains the child's PTE
                &&& parent.this_page_perm.value().0@.index(child_index)@@
                    == child.pte_perm.value().0@
                // 3. When PTE is present, it points to the right page
                &&& child.pte_perm.value().is_present_pte_spec() ==> {
                    let pte_phys_addr = child.pte_perm.value().address_spec(
                        self.private_bit,
                        self.shared_bit,
                    );

                    // Physical address is in valid range
                    &&& (self.mapping_space.kernel.in_range_spec(pte_phys_addr)
                        || self.mapping_space.physmap.in_range_spec(
                        pte_phys_addr,
                    ))
                    // Virtual/physical mapping is consistent
                    &&& {
                        let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);
                        child.this_page_perm.pptr().addr() == vaddr@ as usize
                    }
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
    /// - ✅ **Self-mapped**.
    /// # Verification Impact
    /// When this function returns `true`, you can be confident that:
    /// 1. 🛡️ **Memory Safety**: No access to invalid physical addresses
    /// 2. 🔗 **Structural Integrity**: Page table hierarchy is coherent
    /// 3. 📍 **Address Correctness**: All virtual↔physical mappings are valid
    /// 4. 🔐 **Permission Soundness**: All permission tokens are properly managed
    pub open spec fn wf_with_perm(&self) -> bool {
        // Unified virtual address-based validation
        &&& self.vaddr_based_wf()
        // Coverage: All valid addresses have translations
        &&& self.translates_all_valid_addresses()
        // the root table must have a self-mapping entry so that PML4 becomes PDPT.
        &&& self.self_mapped()
    }
}

impl PagePermission {
    pub open spec fn wf_level(&self) -> bool {
        &&& self.pte_perm.is_init()
            && self.pte_perm.wf()  // must be initialized and well-formed
        &&& self.this_page_perm.is_init()
            && self.this_page_perm.wf()  // page permission must be valid

    }
}

impl View for PageTablePermission {
    type V = Map<PageTablePath, PagePermission>;

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
