// Re-export PTE_BASE from deko-std for backward compatibility
pub use deko_std::address::PTE_BASE;
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

/// Defines a common trait for page table entries.
pub trait PteBehavior: WellFormed + View<V = PhysAddr> {
    spec fn is_valid_pte_spec(&self) -> bool;

    spec fn is_huge_pte_spec(&self) -> bool;

    spec fn is_present_pte_spec(&self) -> bool;

    spec fn page_frame_spec(&self, private_bit: u64) -> (r: PhysAddr);

    spec fn address_spec(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr);

    /// Get the address from the page table entry, including the shared bit.
    fn page_frame(&self, private_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.page_frame_spec(private_bit),
    ;

    /// Get the address from the page table entry, excluding the C/shared bit.
    #[verifier::when_used_as_spec(address_spec)]
    fn address(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.address_spec(private_bit, shared_bit),
    ;

    /// This function checks whether a given PTE is valid in the sense that
    /// it is either not present, or it is huge page so that we will need to
    /// take extra care when handling it.
    fn is_valid_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_valid_pte_spec(&perm.value()),
    ;

    fn is_huge_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_huge_pte_spec(&perm.value()),
    ;

    fn is_present_pte(pte: DekoPPtr<Self>, Tracked(perm): Tracked<&DekoPointsTo<Self>>) -> (r: bool)
        requires
            pte@ == perm.pptr(),
            perm.is_init(),
            perm.wf(),
        ensures
            r == Self::is_present_pte_spec(&perm.value()),
    ;
}

/// Defines a common trait for page table behaviors.
///
/// TODO: Design specs later.
pub trait PageTableBehavior: WellFormed {
    /// Converts a virtual address to a page frame if it is mapped.
    fn virt_to_frame(vaddr: VirtAddr) -> (r: PageFrame);

    /// Walks the page table to find the page table entry for a given virtual address.
    fn walk(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: DekoPagePtr);

    /// Sets a given page as shared.
    fn set_shared_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    );

    /// Maps a single 4KB page at the given virtual address to the given physical address
    fn map_page_4k(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    );
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
pub open spec fn index_at_level_spec(level: nat, vaddr: VirtAddr) -> nat
    recommends
        level < 4,
{
    ((vaddr.0 >> (12 + level * 9)) & 0x1ff) as nat
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

#[allow(inconsistent_fields)]
pub tracked enum PagePermission {
    Level0 { idx: nat, value: PageTableEntry, this_page_perm: DekoPointsTo<Page> },
    LevelN {
        level: nat,  // 1, 2, or 3
        idx: int,
        value: PageTableEntry,
        this_page_perm: DekoPointsTo<Page>,
        next_page_perm: DekoPointsTo<Page>,
    },
}

with_permission! {
    PageTable,
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
}

impl PageTablePermission {
    /// Ensures all PTEs are within the valid physical range.
    pub open spec fn pte_within_range(&self, start_phys: u64, end_phys: u64) -> bool {
        &&& forall|i: (PagePermissionIndex, PagePermission)|
            #![auto]
            self.storage.contains_key(i.0) ==> {
                let pte = match i.1 {
                    PagePermission::Level0 { value, .. } => value,
                    PagePermission::LevelN { value, .. } => value,
                };
                let paddr = pte.address_spec(self.private_bit, self.shared_bit);
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
            new_entry.level() == level,
            new_entry.idx() == idx,
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            // If the key is already present from the map,
            // then its existing value is overwritten by the new value.
            storage: self.storage.insert((level, idx), new_entry),
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
            new_entry.level() == level,
            new_entry.idx() == idx,
            new_entry.wf(),
    {
        PageTablePermission {
            pgtable_perm: self.pgtable_perm,
            storage: self.storage.insert((level, idx), new_entry),
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
            new_entry matches Some(entry) ==> (entry.level() == level && entry.idx() == idx
                && entry.wf()),
    {
        match new_entry {
            Some(entry) => self.add_present_entry(level, idx, entry),
            None => self.remove_non_present_entry(level, idx),
        }
    }

    /// Creates a new PageTablePermission with an empty storage map
    /// Used when initializing a new page table
    pub open spec fn empty(root_perm: DekoPointsTo<PageTable>) -> Self {
        PageTablePermission {
            pgtable_perm: root_perm,
            storage: Map::empty(),
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
        &&& new_entry.level() == level
        &&& new_entry.idx() == idx
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
                new_entry.value().0@ == initial_page_table_value()
            },
            _ => {
                // For non-root levels, ensure proper nesting
                match new_entry.next_page_perm() {
                    Some(next) => next.value().level() == level - 1,
                    None => level == 0  // Only leaf entries can have None
                    ,
                }
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

    /// This is a recursive specification that checks if the storage map
    /// correctly mirrors the actual page table structure down to level `lvl`.
    ///
    /// The mirror property ensures that:
    /// 1. Only present entries are tracked in the storage map
    /// 2. Each tracked entry's physical address matches what's stored in the actual page table
    /// 3. The hierarchy is consistent (parent entries point to child page tables)
    /// 4. Leaf entries (level 0) don't have next_page_perm
    /// 5. Non-present entries are not tracked in the storage map
    pub open spec fn mirrors(&self, lvl: nat) -> bool
        recommends
            0 <= lvl <= 4,
        decreases lvl,
    {
        match lvl as u64 {
            4 => {
                // For the root page table (level 4), we check that:
                // 1. The root entry exists and is well-formed (root is always present)
                // 2. It corresponds to the actual root page table
                &&& self.storage.contains_key((4, 0))
                &&& {
                    let root = self.storage[(4, 0)];
                    &&& root.wf()
                    &&& root.level() == 4 && root.idx() == 0
                    &&& root.this_page_perm().is_init()
                    // The root should point to the initial page table
                    &&& root.value().0@
                        == initial_page_table_value()
                    // Root is always present
                    &&& self.entry_is_present(4, 0, root)
                }
                // Recursively check level 3
                &&& self.mirrors(3)
            },
            3 => {
                // For level 3 (PML4 entries), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        // If an entry is in storage, it must be present and well-formed
                        self.storage.contains_key((3, idx)) ==> {
                            let entry = self.storage[(3, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 3 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(
                                3,
                                idx,
                                entry,
                            )
                            // If this entry points to a next level page table,
                            // then next_page_perm should be Some and well-formed
                            &&& match entry.next_page_perm() {
                                Some(next_perm) => {
                                    &&& next_perm.wf()
                                    // &&& next_perm.level() == 2
                                    // The physical address should match
                                    &&& next_perm.value()@ == entry.value()@
                                },
                                None => true  // Leaf entry (huge page)
                                ,
                            }
                        }
                    }
                    // Recursively check level 2
                &&& self.mirrors(2)
            },
            2 => {
                // For level 2 (PDPT entries), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        self.storage.contains_key((2, idx)) ==> {
                            let entry = self.storage[(2, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 2 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(2, idx, entry)
                            &&& match entry.next_page_perm() {
                                Some(next_perm) => {
                                    &&& next_perm.wf()
                                    // &&& next_perm.level() == 1
                                    &&& next_perm.value()@ == entry.value()@
                                },
                                None => true  // Huge page
                                ,
                            }
                        }
                    }
                    // Recursively check level 1
                &&& self.mirrors(1)
            },
            1 => {
                // For level 1 (PD entries), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        self.storage.contains_key((1, idx)) ==> {
                            let entry = self.storage[(1, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 1 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(1, idx, entry)
                            &&& match entry.next_page_perm() {
                                Some(next_perm) => {
                                    &&& next_perm.wf()
                                    // &&& next_perm.level() == 0
                                    &&& next_perm.value()@ == entry.value()@
                                },
                                None => true  // Huge page
                                ,
                            }
                        }
                    }
                    // Recursively check level 0
                &&& self.mirrors(0)
            },
            0 => {
                // For level 0 (PT entries - leaf level), only track present entries
                &&& forall|idx: int|
                    0 <= idx < PAGE_TABLE_ENTRY as int ==> {
                        self.storage.contains_key((0, idx)) ==> {
                            let entry = self.storage[(0, idx)];
                            &&& entry.wf()
                            &&& entry.level() == 0 && entry.idx() == idx
                            &&& entry.this_page_perm().is_init()
                            // Entry must represent a present PTE
                            &&& self.entry_is_present(
                                0,
                                idx,
                                entry,
                            )
                            // Level 0 entries should never have next_page_perm
                            &&& entry.next_page_perm() matches None
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
        entry.value().is_present_pte_spec()
    }

    // This specification says that for every entry in the storage map,
    // it must be well-formed and match its (level, index) key.
    // Only present entries are required to be in the storage map.
    //
    // This ensures the storage mirrors only the present entries in the actual page table structure.
    pub open spec fn wf_with_perm(&self) -> bool {
        self.mirrors(4)
    }
}

impl PagePermission {
    pub open spec fn level(&self) -> nat {
        match self {
            PagePermission::Level0 { .. } => 0,
            PagePermission::LevelN { level, .. } => *level,
        }
    }

    pub open spec fn idx(&self) -> int {
        match self {
            PagePermission::Level0 { idx, .. } => *idx as int,
            PagePermission::LevelN { idx, .. } => *idx,
        }
    }

    pub open spec fn value(&self) -> PageTableEntry {
        match self {
            PagePermission::Level0 { value, .. } => *value,
            PagePermission::LevelN { value, .. } => *value,
        }
    }

    pub open spec fn this_page_perm(&self) -> DekoPointsTo<Page> {
        match self {
            PagePermission::Level0 { this_page_perm, .. } => *this_page_perm,
            PagePermission::LevelN { this_page_perm, .. } => *this_page_perm,
        }
    }

    pub open spec fn next_page_perm(&self) -> Option<DekoPointsTo<Page>> {
        match self {
            PagePermission::Level0 { .. } => None,
            PagePermission::LevelN { next_page_perm, .. } => Some(*next_page_perm),
        }
    }

    pub open spec fn wf_level(&self) -> bool {
        &&& self.level() <= 4  // must be a valid level
        &&& self.this_page_perm().is_init() && self.this_page_perm().wf()
        &&& { self.level() == 0 <==> self.next_page_perm() matches None }
        &&& { self.level() > 0 <==> { self.next_page_perm() matches Some(pg) ==> pg.wf() } }
        &&& match self {
            PagePermission::Level0 { idx, .. } => 0 <= *idx < PAGE_TABLE_ENTRY,
            PagePermission::LevelN { level, idx, .. } => {
                &&& 1 <= *level <= 3
                &&& 0 <= *idx < PAGE_TABLE_ENTRY as int
            },
        }
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
    Level3(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
    Level2(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
    Level1(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
    Level0(DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>),
}

// PageTableEntry can be safely cast into a Page when it represents a valid, present,
// non-huge page table entry that points to a properly aligned page table.
impl SafeCastInto<Page> for PageTableEntry {
    #[verifier::inline]
    open spec fn cast_valid(&self) -> bool {
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
    type V = (DekoPPtr<PageTableEntry>, Tracked<PagePermissionIndex>);

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.into_inner_spec()
    }
}

impl Mapping {
    pub open spec fn into_inner_spec(&self) -> (
        DekoPPtr<PageTableEntry>,
        Tracked<PagePermissionIndex>,
    ) {
        match self {
            Mapping::Level3(pte, idx) => (*pte, *idx),
            Mapping::Level2(pte, idx) => (*pte, *idx),
            Mapping::Level1(pte, idx) => (*pte, *idx),
            Mapping::Level0(pte, idx) => (*pte, *idx),
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

impl PteBehavior for PageTableEntry {
    open spec fn address_spec(&self, private_bit: u64, shared_bit: u64) -> PhysAddr {
        PhysAddr(
            strip_shared_address_bits_spec(
                strip_confidentiality_bits_spec(self.0.0 & 0x000f_ffff_ffff_f000, private_bit),
                shared_bit,
            ),
        )
    }

    open spec fn page_frame_spec(&self, private_bit: u64) -> PhysAddr {
        PhysAddr(strip_confidentiality_bits_spec(self.0.0 & 0x000f_ffff_ffff_f000, private_bit))
    }

    #[inline]
    fn page_frame(&self, private_bit: u64) -> PhysAddr {
        PhysAddr(strip_confidentiality_bits(self.0.0 & 0x000f_ffff_ffff_f000, private_bit))
    }

    /// Get the address from the page table entry, excluding the C/shared bit.
    #[inline]
    fn address(&self, private_bit: u64, shared_bit: u64) -> PhysAddr {
        PhysAddr(strip_shared_address_bits(self.page_frame(private_bit).0, shared_bit))
    }

    open spec fn is_valid_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0 & Pte_ALL_BITS);
        bits.contains(Pte::PRESENT) && !bits.contains(Pte::HUGE)
    }

    open spec fn is_huge_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0 & Pte_ALL_BITS);
        bits.contains(Pte::HUGE)
    }

    open spec fn is_present_pte_spec(&self) -> bool {
        let bits = from_bits(self@.0 & Pte_ALL_BITS); // bits = set.
        bits.contains(Pte::PRESENT)
    }

    fn is_present_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        ensures
            r == Self::is_present_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT)
    }

    /// This function checks whether a given PTE is valid in the sense that
    /// it is either not present, or it is huge page so that we will need to
    /// take extra care when handling it.
    fn is_valid_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        ensures
            r == Self::is_valid_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT) && !flags.contains(HUGE)
    }

    fn is_huge_pte(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&DekoPointsTo<PageTableEntry>>,
    ) -> (r: bool)
        ensures
            r == Self::is_huge_pte_spec(&perm.value()),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(HUGE)
    }
}

impl PageTableBehavior for PageTable {
    fn virt_to_frame(vaddr: VirtAddr) -> (r: PageFrame) {
        vstd::vpanic!("implement me");
    }

    fn walk(
        pgtable: DekoPPtr<PageTable>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: DekoPagePtr) {
        vstd::vpanic!("implement me");
    }

    fn set_shared_4k(
        pgtable: DekoPPtr<PageTable>,
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

    fn map_page_4k(
        pgtable: DekoPPtr<PageTable>,
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

impl View for DekoPagePtr {
    type V = DekoPPtr<Page>;

    open spec fn view(&self) -> DekoPPtr<Page> {
        self.0
    }
}

impl DekoPagePtr {
    /// Create a `DekoPagePtr` from a valid page table entry so we can access the
    /// page table it points to. Note that since PTE contains the physical address
    /// of the page table; to access the page table it points to, we need to convert
    /// the physical address to a virtual address first.
    pub closed spec fn from_pte_spec<T: PteBehavior>(
        pte: T,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Self) {
        let val = strip_shared_address_bits_spec(
            strip_confidentiality_bits_spec(pte@@ & 0x000f_ffff_ffff_f000, private_bit),
            shared_bit,
        );

        // TODO: Add phys to addr here.

        DekoPagePtr(DekoPPtr(vstd::simple_pptr::PPtr(val as usize, core::marker::PhantomData)))
    }

    #[inline]
    pub fn from_pte(
        ctx: DekoPPtr<DekoCtx>,
        Tracked(ctx_perm): Tracked<&DekoCtxPermission>,
        pte: PageTableEntry,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Self)
        requires
            ctx_perm.wf_with(ctx),
            pte.wf(),
            pte.is_valid_pte_spec(),
        ensures
            r == Self::from_pte_spec(pte, private_bit, shared_bit),
    {
        let paddr = pte.address(private_bit, shared_bit);

        DekoPagePtr(DekoPPtr(vstd::simple_pptr::PPtr(paddr.0 as usize, core::marker::PhantomData)))
    }
}

} // verus!
