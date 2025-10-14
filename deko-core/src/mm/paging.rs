use core::borrow::BorrowMut;

// Re-export PTE_BASE from deko-std for backward compatibility
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::DEKO_FRAME_ALLOCATOR;
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

pub proof fn lemma_index_at_level_spec_lt_page_entry_num(level: nat, vaddr: VirtAddr)
    requires
        level < 4,
        vaddr.wf(),
    ensures
        index_at_level_spec(level, vaddr) < PAGE_TABLE_ENTRY as int,
{
    let vaddr = vaddr@;
    let level = level as u64;
    let idx = (vaddr >> (12 + level * 9) & 0x1ff) as u64;

    assert(idx < 512) by (bit_vector)
        requires
            idx == (vaddr >> (12 + level * 9) & 0x1ff) as u64,

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

pub axiom fn page_size_is_4kb()
    ensures
        core::mem::size_of::<Page>() == PAGE_SIZE as usize,
;

pub axiom fn page_table_entry_size_is_qword()
    ensures
        core::mem::size_of::<PageTableEntry>() == 8,
;

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
    pub pte_perm: PageTableEntry,
    /// The permission to the page at this level.
    pub this_page_perm: DekoPointsTo<Page>,
    /// The abstract model of the page as a sequence.
    pub ghost this_page: Seq<DekoPointsTo<PageTableEntry>>,
}

/// A page table path is a sequence of integers representing the indices
/// at each level of the page table hierarchy.
///
/// [idx3, idx2, idx1, offset] for 4-level page table; the last is the
/// final offset within the mapped physical page.
pub tracked struct PageTablePath(pub Seq<int>);

impl WellFormed for PageTablePath {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        1 <= self@.len() <= 4 && forall|i: int|
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
    ( $($x:expr),* $(,)?) => {
        {
            PageTablePath(seq![$($x),*])
        }
    };
}

impl PageTablePath {
    /// Normalize path by stripping leading self-map indices (493)
    ///
    /// Examples:
    /// - [493, 493, 493, 493] → [493]  (all 493s, keep one)
    /// - [493, 493, 493, 10]  → [10]   (strip leading 493s)
    /// - [493, 493, 10, 20]   → [10, 20]
    /// - [493, 10, 20, 30]    → [10, 20, 30]
    /// - [10, 20, 30, 40]     → [10, 20, 30, 40] (no 493s)
    pub open spec fn normalize(self) -> Self
        recommends
            self.wf(),
    {
        if self.len() == 0 {
            self
        } else if self@[0] != 493 {
            // Doesn't start with 493, no normalization needed
            self
        } else {
            // Starts with 493, need to strip leading 493s
            let stripped = self.strip_leading_self_map();

            if stripped.len() == 0 {
                // All were 493s, keep one
                PageTablePath(seq![493])
            } else {
                // Return the stripped path
                stripped
            }
        }
    }

    /// Strip all leading SELF_MAP_INDEX (493) entries
    pub open spec fn strip_leading_self_map(self) -> Self
        decreases self.len(),
    {
        if self.len() == 0 {
            self
        } else if self@[0] == 493 {
            // First element is 493, strip it and recurse
            PageTablePath(self@.skip(1)).strip_leading_self_map()
        } else {
            // First element is not 493, done
            self
        }
    }

    /// Check if path is already in normalized form
    pub open spec fn is_normalized(self) -> bool {
        self.normalize() == self
    }

    /// Count leading 493s (helper for proofs)
    pub open spec fn count_leading_self_map(self) -> nat
        decreases self.len(),
    {
        if self.len() == 0 || self@[0] != 493 {
            0
        } else {
            1 + PageTablePath(self@.skip(1)).count_leading_self_map()
        }
    }

    /// This proves that from_vaddr and into_vaddr are inverses but because we have address
    /// cacnonicalization, this requires some extra proof effort.
    pub proof fn lemma_from_path_to_path_same(vaddr: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            vaddr@ & !(0xfff) == Self::from_vaddr(vaddr).into_vaddr()@,
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let path = Self::from_vaddr(vaddr);

        assert(path.len() == 4);
        assert(path@[0] as u64 == vaddr@ >> 39 & 0x1ff);
        assert(path@[1] as u64 == vaddr@ >> 30 & 0x1ff);
        assert(path@[2] as u64 == vaddr@ >> 21 & 0x1ff);
        assert(path@[3] as u64 == vaddr@ >> 12 & 0x1ff);

        let vaddr_from_path = path.into_vaddr();
        // Do an expansion.
        assert(vaddr_from_path == VirtAddr::new(
            (path@[0] as u64) << 39 | (path@[1] as u64) << 30 | (path@[2] as u64) << 21 | (
            path@[3] as u64) << 12,
        ));
        let vaddr = vaddr@;
        let raw = (vaddr@ >> 39 & 0x1ff) << 39 | (vaddr@ >> 30 & 0x1ff) << 30 | (vaddr@ >> 21
            & 0x1ff) << 21 | (vaddr@ >> 12 & 0x1ff) << 12;
        assert(vaddr_from_path == VirtAddr::new(raw));
        assert(vaddr_from_path@ == sign_extend_spec(raw));

        // Case by case discussion on the new.
        if raw <= VADDR_LOWER_MASK {
            admit();

        } else if raw < VADDR_RANGE_SIZE {
            admit();

        } else {
            assert(vaddr_from_path@ == sign_extend_impl(raw));
            admit();
        }
    }

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

    pub broadcast proof fn lemma_from_vaddr_at_level_makes_wf(vaddr: VirtAddr, level: nat)
        requires
            level <= 3,
            vaddr.wf(),
        ensures
            #![trigger Self::from_vaddr_at_level(vaddr, level)]
            Self::from_vaddr_at_level(vaddr, level).wf(),
    {
        let res = Self::from_vaddr_at_level(vaddr, level);

        assert(1 <= res.len() <= 4);

        assert forall|i: int| 0 <= i < res.len() implies 0 <= #[trigger] res@[i]
            < PAGE_TABLE_ENTRY as int by {
            assert(res@[i] == index_at_level_spec((3 - i) as nat, vaddr));
            lemma_index_at_level_spec_lt_page_entry_num((3 - i) as nat, vaddr);
        }
    }

    // from_vaddr is just a shorthand for 4KB pages
    #[verifier::inline]
    pub open spec fn from_vaddr(vaddr: VirtAddr) -> Self {
        Self::from_vaddr_at_level(vaddr, 0)
    }

    #[verifier::inline]
    pub open spec fn into_vaddr(&self) -> VirtAddr
        recommends
            self.wf(),
            1 <= self.len() <= 4,
    {
        match self.len() as usize {
            1 => VirtAddr::new(((self@[0] as u64) << 39)),
            2 => VirtAddr::new(((self@[0] as u64) << 39) | ((self@[1] as u64) << 30)),
            3 => VirtAddr::new(
                ((self@[0] as u64) << 39) | ((self@[1] as u64) << 30) | ((self@[2] as u64) << 21),
            ),
            4 => VirtAddr::new(
                ((self@[0] as u64) << 39) | ((self@[1] as u64) << 30) | ((self@[2] as u64) << 21)
                    | ((self@[3] as u64) << 12),
            ),
            _ => VirtAddr::new(0)  // unreachable
            ,
        }
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

impl Page {
    pub axiom fn array_ptr_offset_matches(array_perm: DekoPointsTo<Self>, index: usize)
        requires
            index < PAGE_TABLE_ENTRY as usize,
            Array::<PageTableEntry, PAGE_TABLE_ENTRY>::size_wf(),
            array_perm.wf(),
            array_perm.is_init(),
        ensures
            array_perm.pptr().addr() + (index * core::mem::size_of::<PageTableEntry>())
                == array_perm.value().0.idx_ptr(index as int).addr(),
    ;
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
    pub open spec fn page_frame_spec(&self, private_bit: u64) -> PhysAddr {
        match self {
            PageFrame::Frame4K(paddr) => PhysAddr(
                strip_confidentiality_bits_spec(paddr@, private_bit),
            ),
            PageFrame::Frame2M(paddr) => PhysAddr(
                strip_confidentiality_bits_spec(paddr@, private_bit),
            ),
            PageFrame::Frame1G(paddr) => PhysAddr(
                strip_confidentiality_bits_spec(paddr@, private_bit),
            ),
        }
    }

    pub open spec fn address_spec(&self, private_bit: u64, shared_bit: u64) -> PhysAddr {
        PhysAddr(strip_shared_address_bits_spec(self.page_frame_spec(private_bit)@, shared_bit))
    }

    /// Get the address from the page frame, including the shared bit.
    #[verifier::when_used_as_spec(page_frame_spec)]
    pub fn page_frame(&self, private_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.page_frame_spec(private_bit),
    {
        let paddr = match *self {
            Self::Frame4K(pa) => pa,
            Self::Frame2M(pa) => pa,
            Self::Frame1G(pa) => pa,
        };
        PhysAddr(strip_confidentiality_bits(paddr.0, private_bit))
    }

    /// Get the address from the page frame, excluding the C/shared bit.
    #[verifier::when_used_as_spec(address_spec)]
    pub fn address(&self, private_bit: u64, shared_bit: u64) -> (r: PhysAddr)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.address_spec(private_bit, shared_bit),
    {
        PhysAddr(strip_shared_address_bits(self.page_frame(private_bit).0, shared_bit))
    }
}

impl Page {
    pub open spec fn get_pte_address_spec(vaddr: VirtAddr) -> (r: VirtAddr) {
        let offset = (vaddr@ & 0x0000_FFFF_FFFF_F000u64) >> 9;
        VirtAddr((PTE_BASE@ + offset) as u64)
    }

    pub proof fn lemma_get_pte_address_wf(vaddr: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            Self::get_pte_address_spec(vaddr).wf(),
    {
        let vaddr = vaddr@;
        let addr = (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000u64) >> 9)) as u64;

        assert(addr >= 0xFFFF_8000_0000_0000u64) by (bit_vector)
            requires
                addr == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000u64) >> 9)) as u64,
        ;
    }

    pub proof fn lemma_get_pte_address_align_qword(vaddr: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            Self::get_pte_address_spec(vaddr)@ % 8 == 0,
    {
        let addr = Self::get_pte_address_spec(vaddr)@;
        let vaddr = vaddr@;

        assert(addr % 8 == 0) by (bit_vector)
            requires
                addr == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000u64) >> 9)) as u64,
        ;
    }

    /// Allocates a new page from the page frame allocator.
    ///
    /// This function is unfortunately unverified because the current Verus
    /// tool is yet unable to reason about static variables (only `exec`
    /// functions are allowed); there is no explicit way to reason about
    /// the properties of the frame allocator w.r.t. the mapping space.
    ///
    /// There is not way, for example, to prove the following trivial fact:
    ///
    /// ```rust,ignore
    /// pub exec static DEKO_FRAME_ALLOCATOR: DekoPageFrameAllocator
    ///     ensures
    ///         DEKO_FRAME_ALLOCATOR.wf(),
    /// {
    ///     DekoPageFrameAllocator::new()
    /// }
    ///
    /// DEKO_FRAME_ALLOCATOR.init(some_params);
    ///
    /// proof {
    ///     assert(DEKO_FRAME_ALLOCATOR.heap_region.within(some_params));
    ///     // cannot call spec functions on statics.
    /// }
    /// ```
    /// # Safety
    ///
    /// Calling this function is however safe, because we ensure that the
    /// init function only takes as input a hardcoded memory region that
    /// we guaranteed to be mapped.
    ///
    /// Special note: the pointer is already converted into vaddr.
    #[verifier::external_body]
    pub fn alloc_new(ms: &MappingSpace) -> (r: (
        DekoPPtr<Self>,
        Tracked<DekoPointsTo<Self>>,
        PhysAddr,
    ))
        requires
            ms.wf(),
        ensures
            r.1@.pptr() == r.0@,
            r.1@.is_init(),
            r.1@.wf(),
            ms.phys_to_virt_spec(r.2)@ as usize == r.0.addr(),
            ms.physmap.in_range_spec(r.2) || ms.kernel.in_range_spec(r.2),
    {
        let (ptr, Tracked(prov), Tracked(dealloc)) = DEKO_FRAME_ALLOCATOR.0.alloc(
            PAGE_SIZE as usize,
            0x8,
        );
        // lack proof that the ptr is within the physmap range (how should we do this?)
        let paddr = PhysAddr::from(ptr);
        let vaddr = ms.phys_to_virt(paddr);

        let pptr = DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData));

        (pptr, Tracked::assume_new(), paddr)
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

    #[verifier::spinoff_prover]
    pub fn allocate_pte_4k(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            old(perm).allocate_pte_4k_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            old(perm).allocate_pte_4k_ensures(vaddr, private_bit, shared_bit, r, perm),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let req_mapping = Self::walk(page, Tracked(perm), vaddr, ms, private_bit, shared_bit);

        proof {
            assert(old(perm).walk_ensures(vaddr, req_mapping));
        }

        match req_mapping {
            Mapping::Level0(_) => req_mapping,
            Mapping::Level3(pte) => {
                Self::allocate_pte_lvl3(
                    pte,
                    Tracked(perm),
                    vaddr,
                    ms,
                    private_bit,
                    shared_bit,
                    false,
                )
            },
            _ => vstd::vpanic!("todo"),
        }
    }

    #[verifier::spinoff_prover]
    pub fn allocate_pte_lvl3(
        pte: DekoPPtr<PageTableEntry>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> (r: Mapping)
        requires
            old(perm).allocate_pte_lvl3_requires(pte, vaddr, ms, private_bit, shared_bit, huge),
        ensures
            old(perm).allocate_pte_lvl3_ensures(pte, vaddr, private_bit, shared_bit, huge, r, perm),
    {
        vstd::vpanic!("todo");
        // broadcast use PteFlags::lemma_each_bits_is_valid;
        // broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        // let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 3);
        // // First we need to check if the PTE is already present.
        // // But since we need to modify the permission storage later
        // // and Verus cannot handle a mutable reference to that storage
        // // we have to modify it in place (remove and then re-insert).
        // //
        // // This constraints the borrow rule so we have to let the
        // // borrow be temporary here by putting it in a block.
        // {
        //     let tracked pte_perm = &perm.storage.tracked_borrow(path).pte_perm;

        //     if !PageTableEntry::is_present_pte(pte, Tracked(pte_perm)) {
        //         return Mapping::Level3(pte);
        //     }
        // }

        // // Request a new page frame from the allocator.
        // let (ptr, Tracked(ptr_perm), paddr) = Page::alloc_new(ms);
        // if ptr.addr() == 0 || paddr.0 == 0 {
        //     // Heap does not start with 0 so use 0 to indicate OOM
        //     // is fine; but should we indicate something else here
        //     // or just die?
        //     vstd::vpanic!("Out of memory");
        // }
        // let flags = PteFlags::writeable();
        // let tracked mut page_perm = perm.storage.tracked_remove(path);  // we remove and then re-insert later.
        // let entry = *pte.borrow(Tracked(&page_perm.pte_perm));
        // let new_entry_value = PageTableEntry(
        //     PhysAddr(
        //         make_private_address(entry.0.0, private_bit, shared_bit) | flags.bits() as u64,
        //     ),
        // );
        // pte.write(Tracked(&mut page_perm.pte_perm), new_entry_value);
        // let idx = index_at_level::<2>(vaddr);  // continue next level allocation.
        // let (next_pte, _) = ptr.borrow(Tracked(&ptr_perm)).0.index_as_ptr(idx);
        // // Then give it back.
        // proof {
        //     page_perm.this_page_perm = ptr_perm;  // replace it.
        //     perm.storage.tracked_insert(path, page_perm);
        //     // Also we need to update the next level permission.

        //     let path_0 = path@[0];
        //     let next_path = path![path_0, idx as int];
        //     let next_level_perm = perm.storage.tracked_remove(next_path);
        // }

        // Self::allocate_pte_lvl2(next_pte, Tracked(perm), vaddr, ms, private_bit, shared_bit, huge)
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
            perm.walk_addr_lvl0_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            r == perm.walk_addr_lvl0_spec(vaddr),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let idx = index_at_level::<0>(vaddr);
        let ghost path = PageTablePath::from_vaddr(vaddr);
        let ghost path_0 = path@[0];
        let ghost path_1 = path@[1];
        let ghost path_2 = path@[2];
        let ghost parent_path = path![path_0, path_1, path_2];

        proof {
            assert(parent_path@ == PageTablePath::from_vaddr_at_level(vaddr, 1)@);
        }

        let tracked page_perm = &perm.storage.tracked_borrow(parent_path).this_page_perm;
        let (entry, entry_perm) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);

        Mapping::Level0(entry)
    }

    #[verifier::spinoff_prover]
    pub fn walk_addr_lvl1(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            perm.walk_addr_lvl1_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            r == perm.walk_addr_lvl1_spec(vaddr),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let idx = index_at_level::<1>(vaddr);
        let ghost path = PageTablePath::from_vaddr(vaddr);
        let ghost path_0 = path@[0];
        let ghost path_1 = path@[1];
        let ghost parent_path = path![path_0, path_1];
        let ghost child_path = path![path_0, path_1, idx as int];

        let tracked page_perm = &perm.storage.tracked_borrow(parent_path).this_page_perm;
        proof {
            assert(parent_path@ == PageTablePath::from_vaddr_at_level(vaddr, 2)@);
            assert(child_path@ == PageTablePath::from_vaddr_at_level(vaddr, 1)@);
        }

        let (entry, entry_perm) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);
        if !PageTableEntry::is_valid_pte(entry, entry_perm) {
            Mapping::Level1(entry)
        } else {
            let ghost paddr = entry_perm@.value().address_spec(private_bit, shared_bit);

            proof {
                assert(entry_perm@.value() == page_perm.value().0@.index(idx as int));
                assert(entry_perm@.value().is_present_pte_spec());
                assert(child_path.drop_last()@ == parent_path@);
                assert(perm.storage[child_path].pte_perm == entry_perm@.value());
                assert(ms.kernel.in_range_spec(paddr) || ms.physmap.in_range_spec(paddr));
            }
            let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
            Page::walk_addr_lvl0(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        }
    }

    #[verifier::spinoff_prover]
    pub fn walk_addr_lvl2(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            perm.walk_addr_lvl2_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            r == perm.walk_addr_lvl2_spec(vaddr),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let idx = index_at_level::<2>(vaddr);
        let ghost path = PageTablePath::from_vaddr(vaddr);
        let ghost path_0 = path@[0];
        let ghost parent_path = path![path_0];
        let ghost child_path = path![path_0, idx as int];

        let tracked page_perm = &perm.storage.tracked_borrow(parent_path).this_page_perm;

        proof {
            assert(parent_path@ == PageTablePath::from_vaddr_at_level(vaddr, 3)@);
            assert(child_path@ == PageTablePath::from_vaddr_at_level(vaddr, 2)@);
        }

        let (entry, entry_perm) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);

        if !PageTableEntry::is_valid_pte(entry, entry_perm) {
            Mapping::Level2(entry)
        } else {
            let ghost paddr = entry_perm@.value().address_spec(private_bit, shared_bit);

            proof {
                assert(entry_perm@.value() == page_perm.value().0@.index(idx as int));
                assert(entry_perm@.value().is_present_pte_spec());
                assert(child_path.drop_last()@ == parent_path@);
                assert(perm.storage[child_path].pte_perm == entry_perm@.value());
                assert(ms.kernel.in_range_spec(paddr) || ms.physmap.in_range_spec(paddr));
            }
            let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
            Page::walk_addr_lvl1(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        }

    }

    #[verifier::spinoff_prover]
    pub fn walk_addr_lvl3(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            perm.walk_addr_lvl3_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            r == perm.walk_addr_lvl3_spec(vaddr),
    {
        let idx = index_at_level::<3>(vaddr);
        let tracked page_perm = &perm.storage.tracked_borrow(path![493]).this_page_perm;

        let (entry, entry_perm) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);
        if !PageTableEntry::is_valid_pte(entry, entry_perm) {
            Mapping::Level3(entry)
        } else {
            let ghost paddr = entry_perm@.value().address_spec(private_bit, shared_bit);

            proof {
                // Proof is straightforward: we just leverage the child-parent relationship
                // established by the permission structure to prove that the entry_perm
                // we obtained from the page table entry is exactly the same as the one
                // stored in the permission structure.
                assert(entry_perm@.value() == page_perm.value().0@.index(idx as int));
                assert(entry_perm@.value().is_present_pte_spec());

                let child_path = path![493, idx as int];
                assert(child_path.wf());
                assert(child_path.drop_last()@ == path![493]@);

                assert(perm.storage[child_path].pte_perm == entry_perm@.value());

                assert(ms.kernel.in_range_spec(paddr) || ms.physmap.in_range_spec(paddr));
            }

            let next_page = Page::from_entry(entry, entry_perm, &ms, private_bit, shared_bit);
            Page::walk_addr_lvl2(next_page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
        }
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

    /// Converts a virtual address to a page frame if it is mapped.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(50)]
    pub fn virt_to_frame(
        vaddr: VirtAddr,
        private_bit: u64,
        Tracked(pgtable_perm): Tracked<&PageTablePermission>,
    ) -> (r: Option<PageFrame>)
        requires
            vaddr.wf(),
            pgtable_perm.wf_with_perm(),
            pgtable_perm.self_mapped(),
            private_bit == pgtable_perm.private_bit,
        ensures
            r.wf(),
            r == pgtable_perm.virt_to_frame_spec(vaddr),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;
        // Calculate the vaddr of each level's PTE.

        let pte_addr = Self::get_pte_address(vaddr);
        let pde_addr = Self::get_pte_address(pte_addr);
        let pdpe_addr = Self::get_pte_address(pde_addr);
        let pml4e_addr = Self::get_pte_address(pdpe_addr);

        let ghost pml4e_perm_path = PageTablePath::from_vaddr(pml4e_addr);
        let ghost pdpe_perm_path = PageTablePath::from_vaddr(pdpe_addr);
        let ghost pde_perm_path = PageTablePath::from_vaddr(pde_addr);
        let ghost pte_perm_path = PageTablePath::from_vaddr(pte_addr);
        let ghost vaddr_path = PageTablePath::from_vaddr(vaddr);

        proof {
            Page::lemma_get_pte_address_align_qword(vaddr);
            Page::lemma_get_pte_address_align_qword(pte_addr);
            Page::lemma_get_pte_address_align_qword(pde_addr);
            Page::lemma_get_pte_address_align_qword(pdpe_addr);

            assert(pml4e_perm_path@ == path![493, 493, 493, 493]@) by {
                pgtable_perm.lemma_pte_of_vaddr_cancels_with_self_mapping(vaddr);
            }
            pgtable_perm.lemma_pml4e_always_mapped(pml4e_addr);
            pgtable_perm.lemma_pte_addr_same_as_vaddr_each_level(vaddr);
        }

        let (pml4e, Tracked(pml4e_perm)) = PageTableEntry::read_pte(
            pml4e_addr,
            Tracked(pgtable_perm),
        );
        proof {
            assert(pml4e_perm.value() == pgtable_perm.storage[PageTablePath(
                vaddr_path@.take(1),
            )].pte_perm);
        }

        if !PageTableEntry::is_present_pte(pml4e, Tracked(pml4e_perm))
            || PageTableEntry::is_huge_pte(pml4e, Tracked(pml4e_perm)) {
            return None;
        }
        proof {
            pgtable_perm.lemma_pte_reads_present_can_read_vaddr(pml4e_addr, pdpe_addr);
        }

        let (pdpe, Tracked(pdpe_perm)) = PageTableEntry::read_pte(pdpe_addr, Tracked(pgtable_perm));
        proof {
            assert(pdpe_perm.value() == pgtable_perm.storage[PageTablePath(
                vaddr_path@.take(2),
            )].pte_perm);
        }
        if !PageTableEntry::is_present_pte(pdpe, Tracked(pdpe_perm)) {
            return None;
        }
        if PageTableEntry::is_huge_pte(pdpe, Tracked(pdpe_perm)) {
            proof {
                assert(pdpe_perm.value().page_frame_spec(private_bit)@ + (vaddr@ & 0x3FFF_FFFF) <= (
                0x000F_FFFF_FFFF_FFFF + 0x3FFF_FFFF)) by {
                    pdpe_perm.value().lemma_page_frame_spec_no_overflow(private_bit);
                    let vaddr = vaddr@;
                    assert(vaddr & 0x3FFF_FFFF <= 0x3FFF_FFFF) by (bit_vector);
                }
                pdpe_perm.value().lemma_page_frame_spec_no_overflow(private_bit);
            }

            let pa = pdpe.borrow(Tracked(&pdpe_perm)).page_frame(private_bit).0 + (vaddr.0
                & 0x3FFF_FFFF);
            return Some(PageFrame::Frame1G(PhysAddr(pa)));
        }
        proof {
            pgtable_perm.lemma_pte_reads_present_can_read_vaddr(pdpe_addr, pde_addr);
        }

        let (pde, Tracked(pde_perm)) = PageTableEntry::read_pte(pde_addr, Tracked(pgtable_perm));
        proof {
            assert(pde_perm.value() == pgtable_perm.storage[PageTablePath(
                vaddr_path@.take(3),
            )].pte_perm);
        }

        if !PageTableEntry::is_present_pte(pde, Tracked(pde_perm)) {
            return None;
        }
        if PageTableEntry::is_huge_pte(pde, Tracked(pde_perm)) {
            proof {
                assert(pde_perm.value().page_frame_spec(private_bit)@ + (vaddr@ & 0x1FFFFF) <= (
                0x000F_FFFF_FFFF_FFFF + 0x1FFFFF)) by {
                    pde_perm.value().lemma_page_frame_spec_no_overflow(private_bit);
                    let vaddr = vaddr@;
                    assert(vaddr & 0x1FFFFF <= 0x1FFFFF) by (bit_vector);
                }
                pde_perm.value().lemma_page_frame_spec_no_overflow(private_bit);
            }

            let pa = pde.borrow(Tracked(&pde_perm)).page_frame(private_bit).0 + (vaddr.0
                & 0x1FFFFF);
            return Some(PageFrame::Frame2M(PhysAddr(pa)));
        }
        proof {
            pgtable_perm.lemma_pte_reads_present_can_read_vaddr(pde_addr, pte_addr);
        }
        let (pte, Tracked(pte_perm)) = PageTableEntry::read_pte(pte_addr, Tracked(pgtable_perm));
        proof {
            assert(pte_perm.value() == pgtable_perm.storage[PageTablePath(
                vaddr_path@.take(4),
            )].pte_perm);
        }
        if !PageTableEntry::is_present_pte(pte, Tracked(pte_perm)) {
            return None;
        }
        proof {
            assert(pte_perm.value().page_frame_spec(private_bit)@ + (vaddr@ & 0xFFF) <= (
            0x000F_FFFF_FFFF_FFFF + 0xFFF)) by {
                pte_perm.value().lemma_page_frame_spec_no_overflow(private_bit);
                let vaddr = vaddr@;
                assert(vaddr & 0xFFF <= 0xFFF) by (bit_vector);
            }
            pte_perm.value().lemma_page_frame_spec_no_overflow(private_bit);
        }
        let pa = pte.borrow(Tracked(&pte_perm)).page_frame(private_bit).0 + (vaddr.0 & 0xFFF);
        Some(PageFrame::Frame4K(PhysAddr(pa)))
    }

    /// Walks the page table to find the last valid page table entry for a given virtual address.
    #[inline]
    #[verifier::spinoff_prover]
    pub fn walk(
        pgtable: DekoPPtr<Self>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            perm.walk_requires(pgtable, vaddr, ms, private_bit, shared_bit),
        ensures
            perm.walk_ensures(vaddr, r),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        proof {
            let r = perm.walk_spec(vaddr);
            
        }

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
    pub proof fn lemma_page_frame_spec_no_overflow(&self, private_bit: u64)
        requires
            self.wf(),
        ensures
            self.page_frame_spec(private_bit)@ <= 0x000f_ffff_ffff_f000,
    {
        let inner = self.0.0;
        assert(inner & 0x000f_ffff_ffff_f000 <= 0x000f_ffff_ffff_f000) by (bit_vector);

        let stripped = (inner & 0x000f_ffff_ffff_f000) & !private_bit;
        assert(stripped <= 0x000f_ffff_ffff_f000) by (bit_vector)
            requires
                stripped == (inner & 0x000f_ffff_ffff_f000) & !private_bit,
                inner & 0x000f_ffff_ffff_f000 <= 0x000f_ffff_ffff_f000,

    }

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
            r == perm.value().is_present_pte_spec(),
    {
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PteFlags::lemma_from_bits_single;

        let flags = PteFlags::from_bits_truncate(pte.borrow(Tracked(&perm)).0.0);
        flags.contains(PRESENT)
    }

    /// Reads "PTE" from the data pages.
    ///
    /// Conceptually the reading from huge pages are identical with reading from normal pages
    /// because 2MB or 1GB pages are just contiguous memories that can be indexed into using
    /// the lower bits of the virtual address.
    ///
    /// Thus we can just read the PTE directly from the virtual address as long as we have
    /// verified that the virtual address is indeed mapped to some physical frame.
    #[verifier::inline]
    pub open spec fn read_pte_spec(
        vaddr: VirtAddr,
        pgtable_perm: &PageTablePermission,
    ) -> PageTableEntry {
        let path = PageTablePath::from_vaddr(vaddr);
        let idx = (vaddr@ >> 3) & 0x1ff;  // the index inside the page.

        pgtable_perm.storage[path].this_page_perm.value().0@.index(idx as int)
    }

    /// This is getting a little bit tricky here because the translation of the virtual address
    /// vaddr directly points to some page table entry but we cannot just obtain it by indexing
    /// into the page table due to the limitation that we yet do not have the virtual address
    /// for that level's page table itself.
    ///
    /// Note that we only have: `this_page_perm.virt == phys_to_virt(pte_perm)`
    ///
    /// Of course we can just walk the page table from the root to find the page table entry
    /// and then translate it into virtual address, but that would be inefficient for now.
    ///
    /// # Sefety
    ///
    /// This operation is safe as in the precondition we must enforce that the virtual address
    /// is indeed mapped to some physical frame, which means that the PTE must be present
    /// and valid; also we are reading from that address, which is guaranteed to be aligned
    /// to 8 bytes because of the way we calculate the PTE address from the virtual address.
    ///
    /// This does not perform and cannot perform any semantic check on the underlying virtual
    /// address's type as they are totally hardware primitives treated as u64 by the hardware.
    ///
    /// Determining whether the PTE is valid or not is the responsibility of this function.
    /// However, the overall safety is guaranteed by high-level logic that ensures the reading
    /// corresponding to some PTE addresses by self_mapped page tables, etc.
    #[verifier::external_body]
    #[inline]
    #[must_use = "Consider checking the PTE's content for validity."]
    pub(crate) fn read_pte(
        vaddr: VirtAddr,
        Tracked(pgtable_perm): Tracked<&PageTablePermission>,
    ) -> (r: (DekoPPtr<PageTableEntry>, Tracked<&'static DekoPointsTo<PageTableEntry>>))
        requires
            vaddr.wf(),
            vaddr@ % 0x8 == 0,
            pgtable_perm.wf_with_perm(),
            pgtable_perm.virt_to_frame_spec(vaddr) matches Some(_),
        ensures
            r.1@.value() == Self::read_pte_spec(vaddr, pgtable_perm),
            r.1@.is_init(),
            r.0@ == r.1@.pptr(),
            r.0.addr() == vaddr@ as usize,
            r.1@.wf(),
    {
        let (ptr, Tracked(perm)) = unsafe { DekoPPtr::from_raw_init(vaddr.0) };

        (ptr, Tracked(&perm))
    }
}

impl PageTablePermission {
    /// Get PTE at a given level, with path normalization
    /// Returns a non-present PTE if the path doesn't exist in storage
    pub open spec fn get_pte(&self, path: PageTablePath, level: nat) -> PageTableEntry
        recommends
            level <= 3,
            path.wf(),
    {
        let level_path = PageTablePath(path@.take((4 - level) as int));

        if self.storage.contains_key(level_path) {
            self.storage[level_path].pte_perm
        } else {
            arbitrary()
        }
    }

    #[verifier::inline]
    pub open spec fn allocate_pte_4k_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.walk_requires(page, vaddr, ms, private_bit, shared_bit)
    }

    pub open spec fn allocate_pte_4k_ensures(
        &self,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        res_mapping: Mapping,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        let req_mapping = self.walk_spec(vaddr);

        match req_mapping {
            Mapping::Level0(_) => {
                &&& req_mapping == res_mapping
                &&& new_pgtable_perm == self
            },
            Mapping::Level3(pte) => self.allocate_pte_lvl3_ensures(
                pte,
                vaddr,
                private_bit,
                shared_bit,
                false,
                res_mapping,
                new_pgtable_perm,
            ),
            _ => true,
        }
    }

    pub open spec fn allocate_pte_lvl3_requires(
        &self,
        pte: DekoPPtr<PageTableEntry>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> bool {
        &&& self.wf_with_perm()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let idx = index_at_level_spec(3, vaddr);

            &&& self.storage.contains_key(path![493])
            &&& pte.addr() == self.storage[path![493]].this_page.index(idx).pptr().addr()
            &&& self.storage[path![493]].wf_level()
        }
    }

    pub open spec fn allocate_pte_lvl3_ensures(
        &self,
        pte: DekoPPtr<PageTableEntry>,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
        res_mapping: Mapping,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        true
    }

    /// For naming consistency
    #[verifier::inline]
    pub open spec fn walk_requires(
        &self,
        pgtable: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        self.walk_addr_lvl3_requires(pgtable, vaddr, ms, private_bit, shared_bit)
    }

    #[verifier::inline]
    pub open spec fn walk_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        self.walk_addr_lvl3_spec(vaddr)
    }

    #[verifier::inline]
    pub open spec fn walk_ensures(&self, vaddr: VirtAddr, res_mapping: Mapping) -> bool {
        &&& res_mapping == self.walk_spec(vaddr)
        // &&& match res_mapping {
        //     // we need to ensure that the pte address must be valid.
        //     Mapping::Level3(ptr) => {
        //         let path = PageTablePath::from_vaddr_at_level(vaddr, 3);

        //         &&& ptr.addr() == self.storage[path].pte_perm.pptr().addr()
        //     },
        //     Mapping::Level2(ptr) => {
        //         let path = PageTablePath::from_vaddr_at_level(vaddr, 2);

        //         &&& ptr.addr() == self.storage[path].pte_perm.pptr().addr()
        //     },
        //     Mapping::Level1(ptr) => {
        //         let path = PageTablePath::from_vaddr_at_level(vaddr, 1);

        //         &&& ptr.addr() == self.storage[path].pte_perm.pptr().addr()
        //     },
        //     Mapping::Level0(ptr) => {
        //         let path = PageTablePath::from_vaddr_at_level(vaddr, 0);

        //         &&& ptr.addr() == self.storage[path].pte_perm.pptr().addr()
        //     },
        // }
    }

    pub open spec fn walk_addr_lvl0_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf_with_perm()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 1);

            &&& self.storage.contains_key(path)
            &&& page.addr() == self.storage[path].this_page_perm.pptr().addr()
        }
    }

    pub open spec fn walk_addr_lvl0_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        let pt_path = path;  // Full path [i3, i2, i1, i0]

        let parent_path = PageTablePath(seq![path@[0], path@[1], path@[2]]);
        let idx = path@[3];
        let pte_ptr = self.storage[parent_path].this_page_perm.value().0.idx_ptr(idx);

        Mapping::Level0(pte_ptr)
    }

    pub open spec fn walk_addr_lvl1_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf_with_perm()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 2);

            &&& self.storage.contains_key(path)
            &&& page.addr() == self.storage[path].this_page_perm.pptr().addr()
        }
    }

    pub open spec fn walk_addr_lvl1_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        let pdt_path = PageTablePath(seq![path@[0], path@[1], path@[2]]);
        let parent_path = PageTablePath(seq![path@[0], path@[1]]);
        let idx = path@[2];

        let pte = self.storage[parent_path].this_page_perm.value().0@.index(idx);
        let pte_ptr = self.storage[parent_path].this_page_perm.value().0.idx_ptr(idx);
        if !pte.is_valid_pte_spec() {
            Mapping::Level1(pte_ptr)
        } else {
            self.walk_addr_lvl0_spec(vaddr)
        }
    }

    pub open spec fn walk_addr_lvl2_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf_with_perm()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 3);

            &&& self.storage.contains_key(path)
            &&& page.addr() == self.storage[path].this_page_perm.pptr().addr()
        }
    }

    pub open spec fn walk_addr_lvl2_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        let idx = path@[1];
        let parent_path = PageTablePath(seq![path@[0]]);

        let pte = self.storage[parent_path].this_page_perm.value().0@.index(idx);
        let pte_ptr = self.storage[parent_path].this_page_perm.value().0.idx_ptr(idx);
        if !pte.is_valid_pte_spec() {
            Mapping::Level2(pte_ptr)
        } else {
            self.walk_addr_lvl1_spec(vaddr)
        }
    }

    pub open spec fn walk_addr_lvl3_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf_with_perm()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& self.storage.contains_key(path![493])
        &&& page.addr() == self.storage[path![493]].this_page_perm.pptr().addr()
    }

    pub open spec fn walk_addr_lvl3_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        let idx = path@[0];

        let pte = self.storage[path![493]].this_page_perm.value().0@.index(idx);
        let pte_ptr = self.storage[path![493]].this_page_perm.value().0.idx_ptr(idx);
        if !pte.is_valid_pte_spec() {
            Mapping::Level3(pte_ptr)
        } else {
            self.walk_addr_lvl2_spec(vaddr)
        }
    }

    /// This specification works slightly differently from the walk function which
    /// returns the mapping at the lowest level if possible even if a page is not
    /// mapped at that level.
    ///
    /// However this specification function returns None if the page is not mapped
    /// at intermediate levels.
    pub open spec fn virt_to_frame_spec(&self, vaddr: VirtAddr) -> Option<PageFrame>
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);

        // No more contains_key checks or Option unwrapping!
        let pml4e = self.get_pte(path, 3);
        if !pml4e.is_present_pte_spec() || pml4e.is_huge_pte_spec() {
            None
        } else {
            let pdpe = self.get_pte(path, 2);
            if !pdpe.is_present_pte_spec() {
                None
            } else if pdpe.is_huge_pte_spec() {
                Some(self.make_huge_frame(pdpe, vaddr, 2))
            } else {
                let pde = self.get_pte(path, 1);
                if !pde.is_present_pte_spec() {
                    None
                } else if pde.is_huge_pte_spec() {
                    Some(self.make_huge_frame(pde, vaddr, 1))
                } else {
                    let pte = self.get_pte(path, 0);
                    if !pte.is_present_pte_spec() {
                        None
                    } else {
                        Some(self.make_4kb_frame(pte, vaddr))
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
            2 => self.make_1gb_frame(pte, vaddr),
            1 => self.make_2mb_frame(pte, vaddr),
            _ => arbitrary(),
        }
    }

    // Helper functions
    pub open spec fn make_1gb_frame(&self, pte: PageTableEntry, vaddr: VirtAddr) -> PageFrame {
        let base = pte.page_frame_spec(self.private_bit)@;
        let offset = vaddr.0 & 0x3FFF_FFFF;
        PageFrame::Frame1G(PhysAddr((base + offset) as u64))
    }

    pub open spec fn make_2mb_frame(&self, pte: PageTableEntry, vaddr: VirtAddr) -> PageFrame {
        let base = pte.page_frame_spec(self.private_bit)@;
        let offset = vaddr.0 & 0x1F_FFFF;
        PageFrame::Frame2M(PhysAddr((base + offset) as u64))
    }

    pub open spec fn make_4kb_frame(&self, pte: PageTableEntry, vaddr: VirtAddr) -> PageFrame {
        let base = pte.page_frame_spec(self.private_bit)@;
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

    #[verifier::spinoff_prover]
    pub proof fn lemma_493_prefix_same_this_page_perm(
        &self,
        path_short: PageTablePath,
        path_long: PageTablePath,
    )
        requires
            self.wf_with_perm(),
            path_long.wf() && path_short.wf(),
            path_long@ == seq![493] + path_short@,
        ensures
            self.storage[path_long].this_page_perm.value()
                == self.storage[path_short].this_page_perm.value(),
        decreases path_short.len(),
    {
        let lhs = self.storage[path_short];
        let rhs = self.storage[path_long];

        // Prove PTEs are equal (both from same parent at same index)
        assert(path_long@.drop_last() == seq![493] + path_short@.drop_last());
        let index = path_short@.last();

        // Both PTEs come from reading index from their parents
        // Parents also differ by 493 prefix, so recursively prove equal
        if path_short.len() > 1 {
            let parent_short = PageTablePath(path_short@.drop_last());
            let parent_long = PageTablePath(path_long@.drop_last());
            self.lemma_493_prefix_same_this_page_perm(parent_short, parent_long);
        }
        let lhs_paddr = lhs.pte_perm.address_spec(self.private_bit, self.shared_bit);
        let rhs_paddr = rhs.pte_perm.address_spec(self.private_bit, self.shared_bit);
        let lhs_vaddr = self.mapping_space.phys_to_virt_spec(lhs_paddr);
        let rhs_vaddr = self.mapping_space.phys_to_virt_spec(rhs_paddr);

        assert(lhs.pte_perm == rhs.pte_perm);
        assert(lhs_paddr == rhs_paddr);
        assert(lhs_vaddr == rhs_vaddr);
        assert(lhs.this_page_perm.pptr().addr() == lhs_vaddr@ as usize);
        assert(rhs.this_page_perm.pptr().addr() == rhs_vaddr@ as usize);

        assert(forall|p: PageTablePath| #![auto] p.wf() ==> { self.storage[p].wf_level() });

        self.same_vaddr_reads_same_value(lhs.this_page_perm, rhs.this_page_perm);
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_pte_reads_present_can_read_vaddr(&self, pte_addr: VirtAddr, vaddr: VirtAddr)
        requires
            self.wf_with_perm(),
            pte_addr.wf(),
            vaddr.wf(),
            Page::get_pte_address_spec(vaddr) == pte_addr,
            self.virt_to_frame_spec(pte_addr) matches Some(_),
            PageTableEntry::read_pte_spec(pte_addr, self).is_present_pte_spec(),
        ensures
            self.virt_to_frame_spec(vaddr) matches Some(_),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let pte_path = PageTablePath::from_vaddr(pte_addr);
        let vaddr_path = PageTablePath::from_vaddr(vaddr);
        self.lemma_pte_of_vaddr_shares_prefix(vaddr, pte_addr);

        // Extract necessary indices:
        // pte => [493, a, b, c] [d]
        // vaddr => [a, b, c, d]
        let pte_index_3 = pte_path@[3];
        let pte_index_2 = pte_path@[2];
        let pte_index_1 = pte_path@[1];
        let vaddr_index_3 = vaddr_path@[3];
        let vaddr_index_2 = vaddr_path@[2];
        let vaddr_index_1 = vaddr_path@[1];
        let vaddr_index_0 = vaddr_path@[0];

        assert((pte_addr@ >> 3 & 0x1ff) == vaddr_index_3);
        assert(pte_index_3 == vaddr_index_2);
        assert(pte_index_2 == vaddr_index_1);
        assert(pte_index_1 == vaddr_index_0);

        assert(vaddr_path@.take(1) == path![vaddr_index_0]@);
        assert(vaddr_path@.take(2) == path![vaddr_index_0, vaddr_index_1]@);
        assert(vaddr_path@.take(3) == path![vaddr_index_0, vaddr_index_1, vaddr_index_2]@);
        assert(vaddr_path@.take(4)
            == path![vaddr_index_0, vaddr_index_1, vaddr_index_2, vaddr_index_3]@);
        assert(pte_path@.take(1) == path![493]@);
        assert(pte_path@.take(2) == path![493, vaddr_index_0]@);
        assert(pte_path@.take(3) == path![493, vaddr_index_0, vaddr_index_1]@);
        assert(pte_path@.take(4) == path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2]@);

        let vaddr_3 = self.storage[path![vaddr_index_0]].pte_perm;
        let pte_2 = self.storage[path![493, vaddr_index_0]].pte_perm;

        assert(vaddr_3 == pte_2) by {
            assert(path![493, vaddr_index_0].drop_last()@ == path![493]@);

            assert(pte_2 == self.storage[path![493]].this_page_perm.value().0@.index(
                vaddr_index_0 as int,
            ));  // by page table wellformedness
            assert(vaddr_3 == self.storage[path![493]].this_page_perm.value().0@.index(
                vaddr_index_0 as int,
            ));  // by self-mapped.
        }

        assert(vaddr_3.is_present_pte_spec());

        let vaddr_2 = self.storage[path![vaddr_index_0, vaddr_index_1]].pte_perm;
        let pte_1 = self.storage[path![493, vaddr_index_0, vaddr_index_1]].pte_perm;

        assert(vaddr_2 == pte_1) by {
            assert(path![vaddr_index_0, vaddr_index_1].drop_last()@ == path![vaddr_index_0]@);
            assert(path![493, vaddr_index_0, vaddr_index_1].drop_last()@
                == path![493, vaddr_index_0]@);
            assert(vaddr_2 == self.storage[path![vaddr_index_0]].this_page_perm.value().0@.index(
                vaddr_index_1 as int,
            ));
            assert(pte_1 == self.storage[path![493, vaddr_index_0]].this_page_perm.value().0@.index(
                vaddr_index_1 as int,
            ));  // both by page table wellformedness
            assert(path![493, vaddr_index_0]@ == seq![493] + path![vaddr_index_0]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![vaddr_index_0],
                path![493, vaddr_index_0],
            );
        }

        assert(vaddr_2.is_present_pte_spec());

        if vaddr_2.is_huge_pte_spec() {
            // auto.
        } else {
            let vaddr_1 =
                self.storage[path![vaddr_index_0, vaddr_index_1, vaddr_index_2]].pte_perm;
            let pte_0 =
                self.storage[path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2]].pte_perm;

            assert(vaddr_1 == pte_0) by {
                assert(path![vaddr_index_0, vaddr_index_1, vaddr_index_2].drop_last()@
                    == path![vaddr_index_0, vaddr_index_1]@);
                assert(path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2].drop_last()@
                    == path![493, vaddr_index_0, vaddr_index_1]@);
                assert(vaddr_1
                    == self.storage[path![vaddr_index_0, vaddr_index_1]].this_page_perm.value().0@.index(
                vaddr_index_2 as int));
                assert(pte_0
                    == self.storage[path![493, vaddr_index_0, vaddr_index_1]].this_page_perm.value().0@.index(
                vaddr_index_2 as int));  // both by page table wellformedness
                assert(path![493, vaddr_index_0, vaddr_index_1]@ == seq![493]
                    + path![vaddr_index_0, vaddr_index_1]@);
                self.lemma_493_prefix_same_this_page_perm(
                    path![vaddr_index_0, vaddr_index_1],
                    path![493, vaddr_index_0, vaddr_index_1],
                );
            }

            assert(vaddr_1.is_present_pte_spec());

            if vaddr_1.is_huge_pte_spec() {
                // auto.
            } else {
                let vaddr_0 =
                    self.storage[path![vaddr_index_0, vaddr_index_1, vaddr_index_2, vaddr_index_3]].pte_perm;
                let pte_final =
                    self.storage[path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2]].this_page_perm.value().0@.index(
                vaddr_index_3 as int);

                assert(vaddr_0 == pte_final) by {
                    assert(path![vaddr_index_0, vaddr_index_1, vaddr_index_2, vaddr_index_3].drop_last()@
                        == path![vaddr_index_0, vaddr_index_1, vaddr_index_2]@);
                    assert(vaddr_0
                        == self.storage[path![vaddr_index_0, vaddr_index_1, vaddr_index_2]].this_page_perm.value().0@.index(
                    vaddr_index_3 as int));  // by page table wellformedness
                    assert(pte_final
                        == self.storage[path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2]].this_page_perm.value().0@.index(
                    vaddr_index_3 as int));  // by page table wellformedness
                    assert(path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2]@ == seq![493]
                        + path![vaddr_index_0, vaddr_index_1, vaddr_index_2]@);
                    self.lemma_493_prefix_same_this_page_perm(
                        path![vaddr_index_0, vaddr_index_1, vaddr_index_2],
                        path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2],
                    );
                }

                assert(vaddr_0.is_present_pte_spec()) by {
                    assert(pte_path@ == path![493, vaddr_index_0, vaddr_index_1, vaddr_index_2]@);
                    assert(pte_final == PageTableEntry::read_pte_spec(pte_addr, self));
                }
            }
        }
    }

    /// Verus has no idea of the provenance of `DekoPointsTo` in the paging system,
    /// and by the paging system's design, this is fine.
    pub axiom fn same_vaddr_reads_same_value<V: WellFormed>(
        &self,
        a: DekoPointsTo<V>,
        b: DekoPointsTo<V>,
    )
        requires
            a.wf() && b.wf(),
            a.pptr() == b.pptr(),
            a.is_init() && b.is_init(),
        ensures
            a.value() == b.value(),
    ;

    /// Proves that if two virtual addresses map to the same physical address,
    /// then reading from those virtual addresses yields the same value.
    ///
    /// This axiom is crucial for reasoning about memory consistency in systems
    /// with virtual memory, ensuring that different virtual addresses
    /// that resolve to the same physical memory location will always read
    /// the same value.
    pub axiom fn same_paddr_reads_same_value<V: WellFormed>(
        &self,
        a: DekoPointsTo<V>,
        b: DekoPointsTo<V>,
    )
        requires
            a.wf() && b.wf(),
            a.is_init() && b.is_init(),
            self.virt_to_frame_spec(VirtAddr(a.pptr().addr() as u64)) matches Some(frame)
                ==> self.virt_to_frame_spec(VirtAddr(b.pptr().addr() as u64)) matches Some(frame)
                ==> {
                match frame {
                    PageFrame::Frame4K(paddr) => {
                        // Get the offset within the 4K page
                        let offset_a = a.pptr().addr() & 0xFFF;
                        let offset_b = b.pptr().addr() & 0xFFF;

                        // Calculate the base physical address of the 4K page
                        let start_addr = strip_shared_address_bits_spec(
                            strip_confidentiality_bits_spec(paddr@, self.private_bit),
                            self.shared_bit,
                        );
                        let addr_a = PhysAddr((start_addr + offset_a as u64) as u64);
                        let addr_b = PhysAddr((start_addr + offset_b as u64) as u64);

                        addr_a == addr_b
                    },
                    PageFrame::Frame2M(paddr) => {
                        // Get the offset within the 2M page
                        let offset_a = a.pptr().addr() & 0x1FFFFF;
                        let offset_b = b.pptr().addr() & 0x1FFFFF;

                        // Calculate the base physical address of the 2M page
                        let start_addr = strip_shared_address_bits_spec(
                            strip_confidentiality_bits_spec(paddr@, self.private_bit),
                            self.shared_bit,
                        );
                        let addr_a = PhysAddr((start_addr + offset_a as u64) as u64);
                        let addr_b = PhysAddr((start_addr + offset_b as u64) as u64);

                        addr_a == addr_b
                    },
                    PageFrame::Frame1G(paddr) => {
                        // Get the offset within the 1G page
                        let offset_a = a.pptr().addr() & 0x3FFFFFFF;
                        let offset_b = b.pptr().addr() & 0x3FFFFFFF;

                        // Calculate the base physical address of the 1G page
                        let start_addr = strip_shared_address_bits_spec(
                            strip_confidentiality_bits_spec(paddr@, self.private_bit),
                            self.shared_bit,
                        );
                        let addr_a = PhysAddr((start_addr + offset_a as u64) as u64);
                        let addr_b = PhysAddr((start_addr + offset_b as u64) as u64);

                        addr_a == addr_b
                    },
                }
            },
        ensures
            a.value() == b.value(),
    ;

    pub open spec fn pte_addr_same_as_vaddr_each_level_spec(&self, vaddr: VirtAddr) -> bool
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let pte_addr = Page::get_pte_address_spec(vaddr);
        let pde_addr = Page::get_pte_address_spec(pte_addr);
        let pdpe_addr = Page::get_pte_address_spec(pde_addr);
        let pml4_addr = Page::get_pte_address_spec(pdpe_addr);

        let pte_path = PageTablePath::from_vaddr(pte_addr);
        let pde_path = PageTablePath::from_vaddr(pde_addr);
        let pdpe_path = PageTablePath::from_vaddr(pml4_addr);
        let pml4_path = PageTablePath::from_vaddr(pdpe_addr);
        let vaddr_path = PageTablePath::from_vaddr(vaddr);

        let pte_val = PageTableEntry::read_pte_spec(pte_addr, self);
        let pde_val = PageTableEntry::read_pte_spec(pde_addr, self);
        let pdpe_val = PageTableEntry::read_pte_spec(pdpe_addr, self);
        let pml4e_val = PageTableEntry::read_pte_spec(pml4_addr, self);

        let pml4_vaddr_path = vaddr_path@.take(1);
        let pdpe_vaddr_path = vaddr_path@.take(2);
        let pde_vaddr_path = vaddr_path@.take(3);
        let pte_vaddr_path = vaddr_path@.take(4);

        let pml4_vaddr_val = self.storage[PageTablePath(pml4_vaddr_path)].pte_perm;
        let pdpe_vaddr_val = self.storage[PageTablePath(pdpe_vaddr_path)].pte_perm;
        let pde_vaddr_val = self.storage[PageTablePath(pde_vaddr_path)].pte_perm;
        let pte_vaddr_val = self.storage[PageTablePath(pte_vaddr_path)].pte_perm;

        &&& pml4_vaddr_val == pml4e_val
        &&& pdpe_vaddr_val == pdpe_val
        &&& pde_vaddr_val == pde_val
        &&& pte_vaddr_val == pte_val
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(50)]
    pub proof fn lemma_pte_addr_same_as_vaddr_each_level(&self, vaddr: VirtAddr)
        requires
            self.wf_with_perm(),
            vaddr.wf(),
        ensures
            self.pte_addr_same_as_vaddr_each_level_spec(vaddr),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let pte_addr = Page::get_pte_address_spec(vaddr);
        let pde_addr = Page::get_pte_address_spec(pte_addr);
        let pdpe_addr = Page::get_pte_address_spec(pde_addr);
        let pml4_addr = Page::get_pte_address_spec(pdpe_addr);

        Page::lemma_get_pte_address_wf(vaddr);
        Page::lemma_get_pte_address_wf(pte_addr);
        Page::lemma_get_pte_address_wf(pde_addr);
        Page::lemma_get_pte_address_wf(pdpe_addr);
        Page::lemma_get_pte_address_wf(pml4_addr);

        let vaddr_path = PageTablePath::from_vaddr(vaddr);
        let pte_path = PageTablePath::from_vaddr(pte_addr);
        let pde_path = PageTablePath::from_vaddr(pde_addr);
        let pdpe_path = PageTablePath::from_vaddr(pdpe_addr);
        let pml4_path = PageTablePath::from_vaddr(pml4_addr);

        let vaddr_path_index_0 = vaddr_path@[0];
        let vaddr_path_index_1 = vaddr_path@[1];
        let vaddr_path_index_2 = vaddr_path@[2];
        let vaddr_path_index_3 = vaddr_path@[3];

        let pte_val = PageTableEntry::read_pte_spec(pte_addr, self);
        let pde_val = PageTableEntry::read_pte_spec(pde_addr, self);
        let pdpe_val = PageTableEntry::read_pte_spec(pdpe_addr, self);
        let pml4e_val = PageTableEntry::read_pte_spec(pml4_addr, self);

        self.lemma_pte_of_vaddr_shares_prefix(vaddr, pte_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pte_addr, pde_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pde_addr, pdpe_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pdpe_addr, pml4_addr);

        assert(pte_val == self.storage[PageTablePath(vaddr_path@.take(4))].pte_perm) by {
            let pte_path_index_3 = pte_path@[3];
            let pte_path_index_2 = pte_path@[2];
            let pte_path_index_1 = pte_path@[1];
            let pte_path_index_0 = pte_path@[0];

            assert(pte_path_index_0 == 493);
            assert(vaddr_path_index_0 == pte_path_index_1);
            assert(vaddr_path_index_1 == pte_path_index_2);
            assert(vaddr_path_index_2 == pte_path_index_3);
            assert(vaddr_path_index_3 == pte_addr@ >> 3 & 0x1ff);

            assert(pte_path@
                == path![493, vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]@);
            assert(PageTablePath(vaddr_path@.take(4))@
                == path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2, vaddr_path_index_3]@);
            assert(PageTablePath(vaddr_path@.take(4))@.drop_last()
                == path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]@);

            assert(pte_val == self.storage[pte_path].this_page_perm.value().0@.index(
                vaddr_path_index_3 as int,
            ));

            assert(self.storage[PageTablePath(vaddr_path@.take(4))].pte_perm
                == self.storage[path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2, vaddr_path_index_3]].pte_perm);
            assert(self.storage[PageTablePath(vaddr_path@.take(4))].pte_perm
                == self.storage[path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]].this_page_perm.value().0@.index(
            vaddr_path_index_3 as int));

            #[verusfmt::skip]  // we don't know formatting this breaks the proof
            assert(path![493, vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]@ ==
                   seq![493] + path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2],
                path![493, vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2],
            );
        }

        assert(pde_val == self.storage[PageTablePath(vaddr_path@.take(3))].pte_perm) by {
            let pde_path_index_3 = pde_path@[3];
            let pde_path_index_2 = pde_path@[2];
            let pde_path_index_1 = pde_path@[1];
            let pde_path_index_0 = pde_path@[0];

            assert(pde_path_index_0 == 493);
            assert(pde_path_index_1 == 493);
            assert(vaddr_path_index_0 == pde_path_index_2);
            assert(vaddr_path_index_1 == pde_path_index_3);
            assert(vaddr_path_index_2 == pde_addr@ >> 3 & 0x1ff);

            assert(pde_path@ == path![493, 493, vaddr_path_index_0, vaddr_path_index_1]@);
            assert(PageTablePath(vaddr_path@.take(3))@
                == path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]@);
            assert(PageTablePath(vaddr_path@.take(3))@.drop_last()
                == path![vaddr_path_index_0, vaddr_path_index_1]@);

            assert(pde_val
                == self.storage[path![493, 493, vaddr_path_index_0, vaddr_path_index_1]].this_page_perm.value().0@.index(
            vaddr_path_index_2 as int));
            assert(self.storage[PageTablePath(vaddr_path@.take(3))].pte_perm
                == self.storage[path![vaddr_path_index_0, vaddr_path_index_1, vaddr_path_index_2]].pte_perm);
            assert(self.storage[PageTablePath(vaddr_path@.take(3))].pte_perm
                == self.storage[path![vaddr_path_index_0, vaddr_path_index_1]].this_page_perm.value().0@.index(
            vaddr_path_index_2 as int));
            assert(path![493, 493, vaddr_path_index_0, vaddr_path_index_1]@ == seq![493]
                + path![493, vaddr_path_index_0, vaddr_path_index_1]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![493, vaddr_path_index_0, vaddr_path_index_1],
                path![493, 493, vaddr_path_index_0, vaddr_path_index_1],
            );
            assert(path![493, vaddr_path_index_0, vaddr_path_index_1]@ == seq![493]
                + path![vaddr_path_index_0, vaddr_path_index_1]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![vaddr_path_index_0, vaddr_path_index_1],
                path![493, vaddr_path_index_0, vaddr_path_index_1],
            );
        }

        assert(pdpe_val == self.storage[PageTablePath(vaddr_path@.take(2))].pte_perm) by {
            let pdpe_path_index_3 = pdpe_path@[3];
            let pdpe_path_index_2 = pdpe_path@[2];
            let pdpe_path_index_1 = pdpe_path@[1];
            let pdpe_path_index_0 = pdpe_path@[0];

            assert(pdpe_path_index_0 == 493);
            assert(pdpe_path_index_1 == 493);
            assert(pdpe_path_index_2 == 493);
            assert(vaddr_path_index_0 == pdpe_path_index_3);
            assert(vaddr_path_index_1 == pdpe_addr@ >> 3 & 0x1ff);

            assert(pdpe_path@ == path![493, 493, 493, vaddr_path_index_0]@);
            assert(PageTablePath(vaddr_path@.take(2))@
                == path![vaddr_path_index_0, vaddr_path_index_1]@);
            assert(PageTablePath(vaddr_path@.take(2))@.drop_last() == path![vaddr_path_index_0]@);

            assert(pdpe_val
                == self.storage[path![493, 493, 493, vaddr_path_index_0]].this_page_perm.value().0@.index(
            vaddr_path_index_1 as int));
            assert(self.storage[PageTablePath(vaddr_path@.take(2))].pte_perm
                == self.storage[path![vaddr_path_index_0, vaddr_path_index_1]].pte_perm);
            assert(self.storage[PageTablePath(vaddr_path@.take(2))].pte_perm
                == self.storage[path![vaddr_path_index_0]].this_page_perm.value().0@.index(
                vaddr_path_index_1 as int,
            ));
            assert(path![493, 493, 493, vaddr_path_index_0]@ == seq![493]
                + path![493, 493, vaddr_path_index_0]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![493, 493, vaddr_path_index_0],
                path![493, 493, 493, vaddr_path_index_0],
            );
            assert(path![493, 493, vaddr_path_index_0]@ == seq![493]
                + path![493, vaddr_path_index_0]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![493, vaddr_path_index_0],
                path![493, 493, vaddr_path_index_0],
            );
            assert(path![493, vaddr_path_index_0]@ == seq![493] + path![vaddr_path_index_0]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![vaddr_path_index_0],
                path![493, vaddr_path_index_0],
            );

        }

        assert(pml4e_val == self.storage[PageTablePath(vaddr_path@.take(1))].pte_perm) by {
            let pml4_path_index_3 = pml4_path@[3];
            let pml4_path_index_2 = pml4_path@[2];
            let pml4_path_index_1 = pml4_path@[1];
            let pml4_path_index_0 = pml4_path@[0];

            assert(pml4_path_index_0 == 493);
            assert(pml4_path_index_1 == 493);
            assert(pml4_path_index_2 == 493);
            assert(pml4_path_index_3 == 493);
            assert(vaddr_path_index_0 == pml4_addr@ >> 3 & 0x1ff);

            assert(pml4_path@ == path![493, 493, 493, 493]@);
            assert(PageTablePath(vaddr_path@.take(1))@ == path![vaddr_path_index_0]@);

            assert(pml4e_val
                == self.storage[path![493, 493, 493, 493]].this_page_perm.value().0@.index(
                vaddr_path_index_0 as int,
            ));
            assert(self.storage[PageTablePath(vaddr_path@.take(1))].pte_perm
                == self.storage[path![vaddr_path_index_0]].pte_perm);

            assert(path![493, 493, 493, 493]@ == seq![493] + path![493, 493, 493]@);
            self.lemma_493_prefix_same_this_page_perm(
                path![493, 493, 493],
                path![493, 493, 493, 493],
            );
            assert(path![493, 493, 493]@ == seq![493] + path![493, 493]@);
            self.lemma_493_prefix_same_this_page_perm(path![493, 493], path![493, 493, 493]);
            assert(path![493, 493]@ == seq![493] + path![493]@);
            self.lemma_493_prefix_same_this_page_perm(path![493], path![493, 493]);
        }
    }

    /// **PROOF**: Proves that all self-mapped page table entries share the same "page"
    ///
    /// This proof comes from two parts:
    ///
    /// - 493 is the self-mapping index so that we have
    #[verifier::spinoff_prover]
    pub proof fn lemma_self_mapped_same_page_perm(&self)
        requires
            self.wf_with_perm(),
        ensures
            self.storage[path![493, 493, 493, 493]].this_page_perm.pptr().addr()
                == self.storage[path![493, 493, 493]].this_page_perm.pptr().addr(),
            self.storage[path![493, 493, 493]].this_page_perm.pptr().addr()
                == self.storage[path![493, 493]].this_page_perm.pptr().addr(),
            self.storage[path![493, 493]].this_page_perm.pptr().addr()
                == self.storage[path![493]].this_page_perm.pptr().addr(),
    {
        assert(forall|child_path: PageTablePath|
            #![trigger self.storage[child_path]]
            self.storage.contains_key(child_path) && child_path.len() > 1 ==> {
                let parent_path = child_path.drop_last();
                let child_index = child_path@[child_path.len() - 1];
                let child = self.storage[child_path];
                let parent = self.storage[parent_path];

                // 2. PTE consistency: parent's page contains the child's PTE
                &&& parent.this_page_perm.value().0@.index(child_index).is_present_pte_spec() ==> {
                    let pte_phys_addr = child.pte_perm.address_spec(
                        self.private_bit,
                        self.shared_bit,
                    );

                    &&& parent.this_page_perm.value().0@.index(child_index)
                        == child.pte_perm
                    // Virtual/physical mapping is consistent
                    &&& {
                        let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);
                        child.this_page_perm.pptr().addr() == vaddr@ as usize
                    }
                }
            });

        // 1. 493 == 493, 493
        // We first prove that 493, 493's pte perm comes from where.
        let child_path_493_493 = path![493, 493];
        assert(child_path_493_493.len() > 1);
        assert(self.storage.contains_key(child_path_493_493));
        let parent_path = child_path_493_493.drop_last();
        let child_index = child_path_493_493@[child_path_493_493.len() - 1];
        let child = self.storage[child_path_493_493];
        let parent = self.storage[parent_path];

        assert(child_index == 493 && parent_path@ == path![493]@);
        assert(parent.this_page_perm.value().0@.index(child_index).is_present_pte_spec()) by {
            // entry.this_page_perm.value().0@.index(493)@ == entry.pte_perm@
            assert(parent.this_page_perm.value().0@.index(child_index)@@
                == parent.pte_perm.0@);
            assert(parent.pte_perm.is_present_pte_spec());  // by self_mapped.
        }
        // Ok now we finally enter the body.
        let pte_phys_addr = child.pte_perm.address_spec(self.private_bit, self.shared_bit);

        let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);
        assert(child.this_page_perm.pptr().addr() == vaddr@ as usize);
        assert(child.pte_perm == parent.pte_perm);
        assert(child.this_page_perm.pptr().addr() == parent.this_page_perm.pptr().addr());
        assert(self.storage[path![493, 493]].this_page_perm.pptr().addr()
            == self.storage[path![493]].this_page_perm.pptr().addr());  // QED

        self.same_vaddr_reads_same_value(
            self.storage[path![493, 493]].this_page_perm,
            self.storage[path![493]].this_page_perm,
        );

        // 2. 493, 493, 493's pte perm comes from where.
        let child_path_493_493_493 = path![493, 493, 493];
        assert(child_path_493_493_493.len() > 1);
        assert(self.storage.contains_key(child_path_493_493_493));
        let parent_path = child_path_493_493_493.drop_last();
        let child_index = child_path_493_493_493@[child_path_493_493_493.len() - 1];
        let child = self.storage[child_path_493_493_493];
        let parent = self.storage[parent_path];

        assert(child_index == 493 && parent_path@ == path![493, 493]@);
        assert(parent.this_page_perm.value().0@.index(child_index).is_present_pte_spec()) by {
            assert(self.storage[path![493, 493]].this_page_perm.value()
                == self.storage[path![493]].this_page_perm.value());
            assert(self.storage[path![493]].this_page_perm.value().0@.index(
                child_index,
            ).is_present_pte_spec());
        }

        // reveal the level consistency wellformedness again.
        let pte_phys_addr = child.pte_perm.address_spec(self.private_bit, self.shared_bit);
        let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);
        assert(child.this_page_perm.pptr().addr() == vaddr@ as usize);
        assert(child.pte_perm == parent.pte_perm);
        assert(child.this_page_perm.pptr().addr() == parent.this_page_perm.pptr().addr());
        assert(self.storage[path![493, 493, 493]].this_page_perm.pptr().addr()
            == self.storage[path![493, 493]].this_page_perm.pptr().addr());  // QED

        self.same_vaddr_reads_same_value(
            self.storage[path![493, 493, 493]].this_page_perm,
            self.storage[path![493, 493]].this_page_perm,
        );
        // 3. 493, 493, 493, 493's pte perm comes from where.
        let child_path_493_493_493_493 = path![493, 493, 493, 493];
        assert(child_path_493_493_493_493.len() > 1);
        assert(self.storage.contains_key(child_path_493_493_493_493));
        let parent_path = child_path_493_493_493_493.drop_last();
        let child_index = child_path_493_493_493_493@[child_path_493_493_493_493.len() - 1];
        let child = self.storage[child_path_493_493_493_493];
        let parent = self.storage[parent_path];

        assert(child_index == 493 && parent_path@ == path![493, 493, 493]@);
        assert(parent.this_page_perm.value().0@.index(child_index).is_present_pte_spec()) by {
            assert(self.storage[path![493, 493, 493]].this_page_perm.value()
                == self.storage[path![493, 493]].this_page_perm.value());
            assert(self.storage[path![493, 493]].this_page_perm.value().0@.index(
                child_index,
            ).is_present_pte_spec());
        }

        let pte_phys_addr = child.pte_perm.address_spec(self.private_bit, self.shared_bit);
        let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);
        assert(child.this_page_perm.pptr().addr() == vaddr@ as usize);
        assert(child.pte_perm == parent.pte_perm);
        assert(child.this_page_perm.pptr().addr() == parent.this_page_perm.pptr().addr());
        assert(self.storage[path![493, 493, 493, 493]].this_page_perm.pptr().addr()
            == self.storage[path![493, 493, 493]].this_page_perm.pptr().addr());  // QED
    }

    /// **PROOF**: Proves that the PML4E for any virtual address is always mapped.
    pub proof fn lemma_pml4e_always_mapped(&self, vaddr: VirtAddr)
        requires
            self.wf_with_perm(),
            vaddr.wf(),
            PageTablePath::from_vaddr(vaddr)@ == path![493, 493, 493, 493]@,
        ensures
            self.virt_to_frame_spec(vaddr) matches Some(_),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        assert(path@.take(4) == path![493, 493, 493, 493]@);
        assert(path@.take(3) == path![493, 493, 493]@);
        assert(path@.take(2) == path![493, 493]@);
        assert(path@.take(1) == path![493]@);

        self.lemma_self_mapped_same_page_perm();
        self.same_vaddr_reads_same_value(
            self.storage[path![493, 493, 493, 493]].this_page_perm,
            self.storage[path![493, 493, 493]].this_page_perm,
        );
        self.same_vaddr_reads_same_value(
            self.storage[path![493, 493, 493]].this_page_perm,
            self.storage[path![493, 493]].this_page_perm,
        );
        self.same_vaddr_reads_same_value(
            self.storage[path![493, 493]].this_page_perm,
            self.storage[path![493]].this_page_perm,
        );

        let pml4e = self.get_pte(path, 3);
        assert(pml4e.is_present_pte_spec());

        let pdpe = self.get_pte(path, 2);
        assert(pdpe.is_present_pte_spec()) by {
            let pdpe_path = path![493, 493];
            let parent_path = pdpe_path.drop_last();
            let child_index = pdpe_path@[pdpe_path.len() - 1];
            let child = self.storage[pdpe_path];
            let parent = self.storage[parent_path];

            assert(child_index == 493 && parent_path@ == path![493]@);
        }

        if pdpe.is_huge_pte_spec() {
        } else {
            let pde = self.get_pte(path, 1);

            assert(pde.is_present_pte_spec()) by {
                let pde_path = path![493, 493, 493];
                let parent_path = pde_path.drop_last();
                let child_index = pde_path@[pde_path.len() - 1];
                let child = self.storage[pde_path];
                let parent = self.storage[parent_path];

                assert(child_index == 493 && parent_path@ == path![493, 493]@);

                assert(parent.this_page_perm.value().0@.index(child_index).is_present_pte_spec())
                    by {
                    assert(self.storage[path![493, 493]].this_page_perm.value()
                        == self.storage[path![493]].this_page_perm.value());
                    assert(self.storage[path![493]].this_page_perm.value().0@.index(
                        child_index,
                    ).is_present_pte_spec());
                }
            }

            if pde.is_huge_pte_spec() {
            } else {
                let pte = self.get_pte(path, 0);

                assert(pte.is_present_pte_spec()) by {
                    let pte_path = path![493, 493, 493, 493];
                    let parent_path = pte_path.drop_last();
                    let child_index = pte_path@[pte_path.len() - 1];
                    let child = self.storage[pte_path];
                    let parent = self.storage[parent_path];

                    assert(child_index == 493 && parent_path@ == path![493, 493, 493]@);

                    assert(parent.this_page_perm.value().0@.index(
                        child_index,
                    ).is_present_pte_spec()) by {
                        assert(self.storage[path![493, 493, 493]].this_page_perm.value()
                            == self.storage[path![493, 493]].this_page_perm.value());
                        assert(self.storage[path![493, 493]].this_page_perm.value().0@.index(
                            child_index,
                        ).is_present_pte_spec());
                    }
                }
            }
        }
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
            index_at_level_spec(0, vaddr) == (pte_of_vaddr@ >> 3) & 0x1FF,
            index_at_level_spec(3, pte_of_vaddr) == 493,
    {
        let vaddr = vaddr@;
        let pte_of_vaddr = (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000) >> 9)) as u64;
        let vaddr_3 = (vaddr >> 39) & 0x1FF;
        let vaddr_2 = (vaddr >> 30) & 0x1FF;
        let vaddr_1 = (vaddr >> 21) & 0x1FF;
        let vaddr_0 = (vaddr >> 12) & 0x1FF;

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
        assert(vaddr_0 == (pte_of_vaddr >> 3) & 0x1FF) by (bit_vector)
            requires
                vaddr_0 == (vaddr >> 12) & 0x1FF,
                pte_of_vaddr == (0xFFFFF68000000000 + ((vaddr & 0x0000_FFFF_FFFF_F000)
                    >> 9)) as u64,
        ;

        assert((pte_of_vaddr >> 39) & 0x1FF == 493) by (bit_vector)
            requires
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
                let pte = perm.pte_perm;
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

    /// This spec function says that the storage map (flattened map) should have
    /// a valid translation for every valid virtual address.
    pub open spec fn translates_all_valid_addresses(&self) -> bool {
        &&& forall|path: PageTablePath|
            #![trigger self.storage.contains_key(path)]
            path.wf() ==> {
                // Root cannot be huge pages: we don't support this.
                &&& path.len() == 1 ==> { !self.storage[path].pte_perm.is_huge_pte_spec() }
                &&& self.storage.contains_key(
                    path,
                )
                // Ensures PTE's virtual address points to PTE.
                &&& self.storage[path].wf_level()
                &&& {
                    let paddr = self.storage[path].pte_perm.address_spec(
                        self.private_bit,
                        self.shared_bit,
                    );

                    // Physical address is in valid range
                    &&& (self.mapping_space.kernel.in_range_spec(paddr)
                        || self.mapping_space.physmap.in_range_spec(
                        paddr,
                    ))
                    // Virtual/physical mapping is consistent
                    &&& {
                        let vaddr = self.mapping_space.phys_to_virt_spec(paddr);
                        self.storage[path].this_page_perm.pptr().addr() == vaddr@ as usize
                    }
                }
            }
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
    ///
    /// Note that only PTEs are "conceptually" the same, but at the virtual address level,
    /// they "look" different so we do not enforce that virtual addresses (i.e., this_page_perm)
    /// are the same as this is wrong.
    pub open spec fn self_mapped(&self) -> bool {
        // Only need to ensure the canonical path [493] exists
        &&& self.storage.contains_key(
            path![493],
        )
        // The self-mapping entry is present
        &&& self.storage[path![493]].pte_perm.is_present_pte_spec()
        &&& !self.storage[path![493]].pte_perm.is_huge_pte_spec()
        // The entry points to the root page itself
        &&& {
            let entry = self.storage[path![493]];
            let paddr = entry.pte_perm.address_spec(self.private_bit, self.shared_bit);

            // Physical address is in valid range
            &&& (self.mapping_space.kernel.in_range_spec(paddr)
                || self.mapping_space.physmap.in_range_spec(
                paddr,
            ))
            // Virtual address mapping is consistent
            &&& entry.this_page_perm.pptr().addr() == self.mapping_space.phys_to_virt_spec(
                paddr,
            )@ as usize
            // This entry really points to itself

        }&&& forall|path: PageTablePath|
            path.wf() && path.len() == 1 ==> {
                let entry = self.storage[path];
                // All other entries's PTE comes from 493.
                entry.pte_perm@ == self.storage[path![493]].this_page_perm.value().0@.index(
                    path@[0],
                )@
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
            #![trigger self.storage[child_path]]
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
                //
                // Special note on the huge pages:
                // We still keep the property even if the parent is huge. This is because
                // the property is reversed: if the parent is huge, then the child must not exist.
                //
                // It must follow the standard page translation rules if we hit huge pages then we
                // just stop.
                &&& child.pte_perm == parent.this_page_perm.value().0@.index(child_index)
                &&& parent.this_page_perm.value().0@.index(child_index).is_present_pte_spec() ==> {
                    let pte_phys_addr = child.pte_perm.address_spec(
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

    /// Checks if a given fixed address mapping range is fully mapped in the page table.
    pub open spec fn region_mapped(&self, range: FixedAddressMappingRange) -> bool {
        &&& forall|vaddr: VirtAddr|
            #![trigger self.virt_to_frame_spec(vaddr)]
            range.virt_start@ <= vaddr@ <= range.virt_end@ ==> {
                &&& self.virt_to_frame_spec(vaddr) matches Some(_)
            }
        &&& self.virt_to_frame_spec(range.virt_start) matches Some(pf) && pf.address_spec(
            self.private_bit,
            self.shared_bit,
        ) == range.phys_start
    }

    /// Checks if a given fixed address mapping range has identity mapping.
    ///
    /// Identity mapping means that for every virtual address in the range,
    /// its physical address equals the virtual address value. This is commonly
    /// used for low memory regions and kernel direct mapping where vaddr == paddr.
    ///
    /// # Properties
    ///
    /// For a range with identity mapping:
    /// - Every virtual address `vaddr` in `[range.virt_start, range.virt_end)` maps to
    ///   a physical address `paddr` where `paddr == vaddr`
    /// - The mapping must be present (not unmapped)
    /// - The physical address in the page frame must equal the virtual address
    ///
    /// # Example Use Case
    ///
    /// ```text
    /// // Low memory identity mapping (0 -> 0, 0x1000 -> 0x1000, etc.)
    /// let lowmem_range = FixedAddressMappingRange::new(
    ///     VirtAddr::new(0),
    ///     VirtAddr::new(LOWMEM_END),
    ///     PhysAddr::from(0),
    /// );
    /// assert!(pgtable_perm.identity_mapped(lowmem_range));
    /// ```
    #[verifier::opaque]
    pub closed spec fn identity_mapped(&self, range: FixedAddressMappingRange) -> bool {
        &&& forall|vaddr: VirtAddr|
            #![trigger self.virt_to_frame_spec(vaddr)]
            range.virt_start@ <= vaddr@ < range.virt_end@ && vaddr.wf() ==> {
                // The virtual address must be mapped
                &&& self.virt_to_frame_spec(vaddr) matches Some(
                    frame,
                )
                // The physical address in the frame must equal the virtual address
                &&& frame.address_spec(self.private_bit, self.shared_bit)@ == vaddr@
            }
    }
}

impl PagePermission {
    pub open spec fn wf_level(&self) -> bool {
        &&& self.this_page_perm.is_init() && self.this_page_perm.wf()
        &&& self.this_page_perm.pptr().addr() % (PAGE_SIZE as usize)
            == 0  // Page must be page-aligned
        &&& self.this_page.len() == PAGE_TABLE_ENTRY
        &&& forall|i: int|
            #![trigger self.this_page.index(i)]
            0 <= i < PAGE_TABLE_ENTRY as int ==> {
                &&& self.this_page.index(i).wf()
                &&& self.this_page.index(i).is_init()
                &&& self.this_page.index(i).pptr() == self.this_page_perm.value().0.idx_ptr(
                    i,
                )@
                // just for easier reasoning later
                &&& self.this_page.index(i).value() == self.this_page_perm.value().0@.index(i)
            }
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
    Level3(DekoPPtr<PageTableEntry>),
    Level2(DekoPPtr<PageTableEntry>),
    Level1(DekoPPtr<PageTableEntry>),
    Level0(DekoPPtr<PageTableEntry>),
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
        true
    }
}

impl View for Mapping {
    type V = DekoPPtr<PageTableEntry>;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.into_inner_spec()
    }
}

impl Mapping {
    pub open spec fn into_inner_spec(&self) -> DekoPPtr<PageTableEntry> {
        match self {
            Mapping::Level3(pte) => *pte,
            Mapping::Level2(pte) => *pte,
            Mapping::Level1(pte) => *pte,
            Mapping::Level0(pte) => *pte,
        }
    }

    pub open spec fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Mapping::Level3(pte1), Mapping::Level3(pte2)) => pte1@ === pte2@,
            (Mapping::Level2(pte1), Mapping::Level2(pte2)) => pte1@ === pte2@,
            (Mapping::Level1(pte1), Mapping::Level1(pte2)) => pte1@ === pte2@,
            (Mapping::Level0(pte1), Mapping::Level0(pte2)) => pte1@ === pte2@,
            _ => false,
        }
    }

    #[verifier::inline]
    pub open spec fn level_spec(&self) -> usize {
        match self {
            Mapping::Level3(_) => 3,
            Mapping::Level2(_) => 2,
            Mapping::Level1(_) => 1,
            Mapping::Level0(_) => 0,
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
            Mapping::Level3(_) => 3,
            Mapping::Level2(_) => 2,
            Mapping::Level1(_) => 1,
            Mapping::Level0(_) => 0,
        }
    }
}

impl View for DekoPagePtr {
    type V = DekoPPtr<Page>;

    open spec fn view(&self) -> DekoPPtr<Page> {
        self.0
    }
}

} // verus!
