use core::borrow::BorrowMut;

use deko_std::prelude::*;
use vstd::pervasive::arbitrary;
// Re-export PTE_BASE from deko-std for backward compatibility
use vstd::{assert_by_contradiction, prelude::*};

use super::DEKO_MAPPING_SPACE;
use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::DEKO_FRAME_ALLOCATOR;
use crate::{log_hex_prefixed, log_str, log_str_ln, Stage2LaunchInfo};

extern "C" {
    #[link_name = "pgtable"]
    pub static mut pgtable__: Page;
}

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

pub const RECURSIVE_INDEX: u64 = 493;

#[verifier::inline]
pub open spec fn bit_not_overlapping(bit: u64) -> bool {
    Pte_ALL_BITS as u64 & bit == 0
}

#[verifier::inline]
pub open spec fn bit_not_in_addr_region(bit: u64) -> bool {
    bit & 0x000f_ffff_ffff_f000u64 == 0
}

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

/// **PROOF**: Verifies that private address transformation is invertible.
///
/// This lemma proves that when you create a PTE by combining a physical address with
/// confidentiality bits and flags, extracting the address back yields the original
/// physical address. This invertibility property is fundamental for ensuring that
/// confidential computing transformations preserve address integrity.
#[verifier::spinoff_prover]
pub proof fn lemma_private_address_transformation_is_invertible(
    private_bit: u64,
    shared_bit: u64,
    pte: PageTableEntry,
    paddr: u64,
    flags: PteFlags,
)
    requires
        bit_not_in_addr_region(private_bit),
        bit_not_in_addr_region(shared_bit),
        flags.wf(),
        flags.bits() & Pte_ALL_BITS == flags.bits(),
        pte@@ == make_private_address_spec(paddr, private_bit, shared_bit) | flags.bits() as u64,
        paddr % 0x1000 == 0,
        paddr < 0x000f_ffff_ffff_f000,
    ensures
        pte.address_spec(private_bit, shared_bit)@ == paddr,
{
    bit_u64_and_auto();

    let pte_addr = pte@@;
    let flags_bits = flags.bits() as u64;
    let addr_extracted = pte.address_spec(private_bit, shared_bit)@;
    let pte_all = (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (1u64 << 7)
        | (1u64 << 8) | (1u64 << 63);

    // Unfold the definitions.
    assert(pte_addr == (paddr & !shared_bit) | private_bit | flags_bits);
    assert(addr_extracted == (pte_addr & 0x000f_ffff_ffff_f000) & !private_bit & !shared_bit);

    assert(paddr == addr_extracted) by (bit_vector)
        requires
            pte_addr == paddr & !shared_bit | private_bit | flags_bits,
            addr_extracted == (pte_addr & 0x000f_ffff_ffff_f000) & !private_bit & !shared_bit,
            private_bit & 0x000f_ffff_ffff_f000 == 0,
            shared_bit & 0x000f_ffff_ffff_f000 == 0,
            pte_all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (1u64
                << 7) | (1u64 << 8) | (1u64 << 63),
            flags_bits & pte_all == flags_bits,
            paddr % 0x1000 == 0,
            paddr < 0x000f_ffff_ffff_f000,
    ;
}

/// **PROOF**: Ensures confidentiality bits don't interfere with PTE flag preservation.
///
/// This lemma proves that when creating a private address with flags, the original
/// PTE flags are preserved despite the addition of confidentiality bits. This is
/// essential for confidential computing environments where private/shared bits
/// must not corrupt page table flag semantics.
#[verifier::spinoff_prover]
pub proof fn lemma_private_bit_non_interfering(
    private_bit: u64,
    shared_bit: u64,
    paddr: u64,
    flags: PteFlags,
)
    requires
        bit_not_overlapping(private_bit),
        bit_not_overlapping(shared_bit),
        flags.wf(),
        flags.bits() & Pte_ALL_BITS == flags.bits(),
        paddr % 0x1000 == 0,
        paddr < 0x000f_ffff_ffff_f000,
    ensures
        ({
            let addr_after = make_private_address_spec(paddr, private_bit, shared_bit);
            let addr_after_pte = addr_after | (flags.bits() as u64);
            let pte_flag = from_bits(addr_after_pte & Pte_ALL_BITS);

            &&& forall|p: Pte| #[trigger] flags@.contains(p) ==> pte_flag.contains(p)
            &&& forall|p: Pte| !#[trigger] flags@.contains(p) ==> !pte_flag.contains(p)
        }),
{
    let addr_after = make_private_address_spec(paddr, private_bit, shared_bit);
    let addr_after_pte = addr_after | (flags.bits() as u64);
    let pte_all = (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (1u64 << 7)
        | (1u64 << 8) | (1u64 << 63);
    let pte_flag = from_bits(addr_after_pte & pte_all);
    let flags_bits = flags.bits() as u64;

    bit_u64_and_auto();

    // Unfold everything.
    assert(private_bit & pte_all as u64 == 0);
    assert(shared_bit & pte_all as u64 == 0);
    assert(addr_after_pte == ((paddr & !shared_bit) | private_bit) | flags_bits);
    assert(pte_flag =~= vstd::set::Set::new(|p: Pte| p.bit() & (addr_after_pte & pte_all) != 0));

    // We want to merge these two foralls but Verus's parser does not
    // recognize two `implies` in a row as a single expression.
    assert forall|p: Pte| #[trigger] flags@.contains(p) implies pte_flag.contains(p) by {
        bit_u64_and_auto();

        let p_bit = p.bit() as u64;
        assert(p_bit & (addr_after_pte & pte_all) != 0) by (bit_vector)
            requires
                p_bit & flags_bits != 0,
                pte_all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (
                1u64 << 7) | (1u64 << 8) | (1u64 << 63),
                addr_after_pte == ((paddr & !shared_bit) | private_bit) | (flags_bits),
                private_bit & pte_all == 0,
                shared_bit & pte_all == 0,
                flags_bits & pte_all == flags_bits,
        ;
    }

    assert forall|p: Pte| !#[trigger] flags@.contains(p) implies !pte_flag.contains(p) by {
        bit_u64_and_auto();

        let p_bit = p.bit() as u64;
        assert(p_bit & (addr_after_pte & pte_all) == 0) by (bit_vector)
            requires
                p_bit & flags_bits == 0,
                pte_all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (
                1u64 << 7) | (1u64 << 8) | (1u64 << 63),
                addr_after_pte == ((paddr & !shared_bit) | private_bit) | (flags_bits),
                private_bit & pte_all == 0,
                shared_bit & pte_all == 0,
                flags_bits & pte_all == flags_bits,
                paddr % 0x1000 == 0,
                paddr < 0x000f_ffff_ffff_f000,
        ;
    }
}

/// **PROOF**: Proves that private address transformation preserves valid memory range membership.
///
/// This lemma establishes that when a physical address is transformed with confidentiality
/// bits and then extracted back through `address_spec()`, it remains within the same valid
/// memory ranges (kernel or physmap). Critical for confidential computing address integrity.
#[verifier::spinoff_prover]
pub proof fn lemma_private_addr_in_range(
    paddr: PhysAddr,
    paddr_priv: PageTableEntry,
    flags: PteFlags,
    ms: &MappingSpace,
    private_bit: u64,
    shared_bit: u64,
)
    requires
        ms.wf(),
        flags.wf(),
        flags.bits() & Pte_ALL_BITS == flags.bits(),
        ms.kernel.in_range_spec(paddr) || ms.physmap.in_range_spec(paddr),
        paddr_priv@@ == make_private_address_spec(paddr@, private_bit, shared_bit)
            | flags.bits() as u64,
        bit_not_in_addr_region(private_bit),
        bit_not_in_addr_region(shared_bit),
    ensures
        ms.kernel.in_range_spec(paddr_priv.address_spec(private_bit, shared_bit))
            || ms.physmap.in_range_spec(paddr_priv.address_spec(private_bit, shared_bit)),
{
    let kernel_phys_start = ms.kernel.phys_start@ as u64;
    let kernel_phys_end = (ms.kernel.virt_end@ - ms.kernel.virt_start@
        + ms.kernel.phys_start@) as u64;
    let physmap_phys_start = ms.physmap.phys_start@ as u64;
    let physmap_phys_end = (ms.physmap.virt_end@ - ms.physmap.virt_start@
        + ms.physmap.phys_start@) as u64;
    let pte_all = (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (1u64 << 7)
        | (1u64 << 8) | (1u64 << 63);

    // Unfold the definitions.
    let paddr_priv_addr = paddr_priv.address_spec(private_bit, shared_bit)@;
    let paddr_priv = paddr_priv@@;
    let paddr = paddr@;
    let flags_bit = flags.bits() as u64;

    assert(paddr_priv == paddr & !shared_bit | private_bit | flags_bit);
    assert(paddr_priv_addr == (paddr_priv & 0x000f_ffff_ffff_f000) & !private_bit & !shared_bit);

    assert(paddr_priv_addr == paddr & 0x000f_ffff_ffff_f000) by (bit_vector)
        requires
            paddr_priv_addr == (paddr_priv & 0x000f_ffff_ffff_f000) & !private_bit & !shared_bit,
            paddr_priv == paddr & !shared_bit | private_bit | flags_bit,
            private_bit & 0x000f_ffff_ffff_f000 == 0,
            shared_bit & 0x000f_ffff_ffff_f000 == 0,
            flags_bit & pte_all == flags_bit,
            pte_all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (1u64
                << 7) | (1u64 << 8) | (1u64 << 63),
    ;

    // by well-formedness of mapping space.
    assert(kernel_phys_end <= 0x000f_ffff_ffff_f000 && physmap_phys_end <= 0x000f_ffff_ffff_f000);
    assert(kernel_phys_start <= paddr & 0x000f_ffff_ffff_f000 < kernel_phys_end
        || physmap_phys_start <= paddr & 0x000f_ffff_ffff_f000 < physmap_phys_end) by (bit_vector)
        requires
            kernel_phys_start % 0x1000 == 0,
            physmap_phys_start % 0x1000 == 0,
            kernel_phys_start <= paddr < kernel_phys_end || physmap_phys_start <= paddr
                < physmap_phys_end,
            kernel_phys_end <= 0x000f_ffff_ffff_f000,
            physmap_phys_end <= 0x000f_ffff_ffff_f000,
    ;
}

/// This function calculates the index at a given level L in the 4-level page table
/// hierarchy for a given virtual address `vaddr`.
#[verus_spec(r =>
    requires
        L < 4,
    ensures
        r < PAGE_TABLE_ENTRY,
        r as int == index_at_level_spec(L as nat, vaddr),
)]  // verus_spec errors for impl blocks so now we only rewrite isolated functions.
#[inline]
pub fn index_at_level<const L: usize>(vaddr: VirtAddr) -> usize {
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

pub broadcast proof fn lemma_index_at_level_spec_lt_page_entry_num(level: nat, vaddr: VirtAddr)
    requires
        level < 4,
        vaddr.wf(),
    ensures
        #[trigger] index_at_level_spec(level, vaddr) < PAGE_TABLE_ENTRY as int,
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
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&DekoCpuCtxPermission>
    requires
        paddr.wf(),
        ctx_perm.wf_with(ctx),
        ctx_perm.pgtable_perm.mapping_space.physmap.in_range_spec(paddr)
            || ctx_perm.pgtable_perm.mapping_space.kernel.in_range_spec(paddr),
    ensures
        r.wf(),
        r == phys_to_virt_spec(ctx_perm.pgtable_perm.mapping_space, paddr),
)]
#[inline(always)]
pub fn phys_to_virt(ctx: DekoPPtr<DekoCpuCtx>, paddr: PhysAddr) -> VirtAddr {
    let ms = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).kernel_mapping();

    ms.phys_to_virt(paddr)
}

deko_bitflags_quick! {
    Pte,
    data: { PRESENT, WRITABLE, USER, ACCESSED, DIRTY, GLOBAL, NX },
    writeable: { PRESENT, USER, WRITABLE, ACCESSED, DIRTY },
    writeable_kernel: { PRESENT, WRITABLE, ACCESSED, DIRTY },
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

pub axiom fn page_is_aligned()
    ensures
        core::mem::align_of::<Page>() == PAGE_SIZE as usize,
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
}

/// A page table path is a sequence of integers representing the indices
/// at each level of the page table hierarchy.
///
/// [idx3, idx2, idx1, offset] for 4-level page table; the last is the
/// final offset within the mapped physical page.
#[verifier::ext_equal]
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
    /// Normalizes a page table path by removing all leading recursive indices.
    ///
    /// In a recursive page table setup, the page table maps itself at a specific
    /// index (typically 493 on x86_64). This creates "shortcut" paths where
    /// `[493, a, b]` and `[a, b]` refer to the **same physical entry**.
    ///
    /// Normalization removes these redundant recursive prefixes to ensure a
    /// **canonical representation**, preventing duplicate ownership issues in
    /// verification.
    ///
    /// # Algorithm
    ///
    /// Recursively removes leading indices that match `recursive_idx` until:
    /// - The path is empty, OR
    /// - The first index is not the recursive index
    ///
    /// # Examples
    ///
    /// ```rust
    /// use PageTablePath;
    /// const RECURSIVE_INDEX: u64 = 493;
    ///
    /// // Already normalized - no change
    /// let path = PageTablePath(seq![100, 200, 300]);
    /// assert(path.normalize() == path);
    ///
    /// // Single recursive prefix removed
    /// let path = PageTablePath(seq![493, 100, 200]);
    /// assert(path.normalize() == PageTablePath(seq![100, 200]));
    ///
    /// // Multiple recursive prefixes removed
    /// let path = PageTablePath(seq![493, 493, 493, 50]);
    /// assert(path.normalize() == PageTablePath(seq![50]));
    ///
    /// // Recursive index in middle - NOT removed (only leading)
    /// let path = PageTablePath(seq![100, 493, 200]);
    /// assert(path.normalize() == path);
    ///
    /// // Path to PML4 itself
    /// let path = PageTablePath(seq![493]);
    /// assert(path.normalize() == PageTablePath(seq![]));
    /// ```
    ///
    /// # Why This Matters for Verification
    ///
    /// Without normalization, Verus would treat `[493, a]` and `[a]` as
    /// **distinct** paths, leading to:
    /// - Duplicate ownership of the same physical page
    /// - Inability to prove uniqueness invariants
    /// - Violation of linear type guarantees
    ///
    /// ```text
    /// // Without normalization (WRONG):
    /// perm1: PagePermission for path [493, 100]
    /// perm2: PagePermission for path [100]
    /// // Both claim ownership of the SAME physical entry!
    ///
    /// // With normalization (CORRECT):
    /// perm1: PagePermission for path [100]  // normalized from [493, 100]
    /// perm2: PagePermission for path [100]  // already normalized
    /// // Now we can prove they're the same and prevent duplication
    /// ```
    ///
    /// # Properties
    ///
    /// The normalization function satisfies several key properties:
    ///
    /// - **Idempotent**: `p.normalize().normalize() == p.normalize()`
    /// - **Decreasing**: `p.normalize().len() <= p.len()`
    /// - **Prefix-preserving**: Non-recursive prefixes are unchanged
    /// - **Equivalence**: Paths with same normalization access same physical entry
    ///
    /// # Recursive Mapping Background
    ///
    /// In x86_64 recursive page tables, PML4[493] points to the PML4 itself.
    /// This creates a "loop":
    ///
    /// ```text
    /// PML4[493] → PML4 (points to itself)
    ///
    /// Accessing [493, a]:
    ///   1. Start at PML4
    ///   2. Follow PML4[493] → back to PML4
    ///   3. Follow PML4[a] → some PDPT
    ///
    /// Accessing [a]:
    ///   1. Start at PML4
    ///   2. Follow PML4[a] → same PDPT
    ///
    /// Result: [493, a] and [a] are IDENTICAL!
    /// ```
    ///
    /// See also: [OS Dev Wiki on Recursive Mapping](https://wiki.osdev.org/Page_Tables#Recursive_mapping)
    ///
    /// # Verification Notes
    ///
    /// This is a `spec` function, computed at verification time only.
    /// The decreasing measure ensures termination.
    ///
    /// # See Also
    ///
    /// - [`Self::remove_recursive_prefix`]: The internal recursive implementation
    #[verifier::inline]
    pub open spec fn normalize(self) -> Self {
        self.remove_recursive_prefix(RECURSIVE_INDEX)
    }

    /// Internal recursive helper for path normalization.
    ///
    /// Removes leading indices matching `recursive_idx` from the path.
    ///
    /// # Parameters
    ///
    /// - `recursive_idx`: The index used for recursive mapping (e.g., 493)
    ///
    /// # Termination
    ///
    /// The function decreases on `self.0.len()`, ensuring termination:
    /// - Base case: Empty path or non-matching first index
    /// - Recursive case: Removes one element and recurs on shorter path
    ///
    /// # Examples
    ///
    /// ```rust
    /// let path = PageTablePath(seq![493, 493, 100]);
    ///
    /// // First recursion: removes first 493
    /// // path = [493, 100], len = 2
    ///
    /// // Second recursion: removes second 493
    /// // path = [100], len = 1
    ///
    /// // Base case: 100 != 493, stop
    /// // result = [100]
    /// ```
    pub open spec fn remove_recursive_prefix(self, recursive_idx: u64) -> Self
        decreases self@.len(),
    {
        if self@.len() > 0 && self@[0] == recursive_idx {
            // Remove the first element and recurse
            PageTablePath(self@.subrange(1, self@.len() as int)).remove_recursive_prefix(
                recursive_idx,
            )
        } else {
            // Base case: empty or first element is not recursive index
            self
        }
    }

    /// Returns true if the path is already normalized.
    #[verifier::inline]
    pub open spec fn is_normalized(self) -> bool {
        self == self.normalize()
    }

    /// Takes the first `n` indices from the page table path.
    #[verifier::inline]
    pub open spec fn take(self, n: int) -> Self
        recommends
            n <= self.len(),
    {
        PageTablePath(self@.take(n))
    }

    pub broadcast proof fn lemma_path_take_fact(vaddr: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            #![trigger Self::from_vaddr(vaddr)]
            ({
                let path = Self::from_vaddr(vaddr);
                let path0 = path@[0];
                let path1 = path@[1];
                let path2 = path@[2];
                let path3 = path@[3];

                &&& path![path0, path1, path2, path3]@ == path@.take(4)
                &&& path![path0, path1, path2]@ == path@.take(3)
                &&& path![path0, path1]@ == path@.take(2)
                &&& path![path0]@ == path@.take(1)
                &&& path![]@ == path@.take(0)
            }),
    {
    }

    pub broadcast proof fn lemma_page_table_path_drop_last_normalize_exchangeable(self)
        requires
            self.wf(),
        ensures
            #![trigger self.drop_last().normalize()]
            #![trigger self.normalize().drop_last()]
            self.normalize().len() > 0 ==> self.normalize().drop_last()
                == self.drop_last().normalize(),
    {
        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);
    }

    pub broadcast proof fn lemma_page_table_path_drop_last_implies(vaddr: VirtAddr, lvl: nat)
        requires
            vaddr.wf(),
            1 < lvl < 4,
        ensures
            #![trigger Self::from_vaddr_at_level(vaddr, lvl)]
            Self::from_vaddr_at_level(vaddr, lvl)@ == Self::from_vaddr_at_level(
                vaddr,
                (lvl - 1) as nat,
            ).drop_last()@,
    {
    }

    pub broadcast proof fn lemma_drop_last(self)
        requires
            self.wf(),
        ensures
            #![trigger self.drop_last()]
            self.drop_last()@ == self@.drop_last(),
    {
    }

    #[verifier::inline]
    pub open spec fn eq(&self, other: &Self) -> bool
        recommends
            self.wf() && other.wf(),
    {
        self.normalize()@ == other.normalize()@
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

    pub broadcast proof fn lemma_get_pte_address_wf(vaddr: VirtAddr)
        requires
            vaddr.wf(),
        ensures
            (#[trigger] Self::get_pte_address_spec(vaddr)).wf(),
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
    ///
    /// FIXME: Possibly we need to revisit this.
    #[verifier::external_body]
    pub fn alloc_new(ms: &MappingSpace) -> (r: (
        DekoPPtr<Self>,
        Tracked<DekoPointsTo<Self>>,
        PhysAddr,
    ))
        requires
            ms.wf(),
        ensures
            r.0.addr() % PAGE_SIZE as usize == 0,
            r.2@ % PAGE_SIZE == 0,
            r.1@.pptr() == r.0@,
            r.1@.is_init(),
            r.1@.wf(),
            r.1@.value().0@.len() as usize == PAGE_TABLE_ENTRY,
            ms.phys_to_virt_spec(r.2)@ as usize == r.0.addr(),
            ms.physmap.in_range_spec(r.2) || ms.kernel.in_range_spec(r.2),
            forall|i: int|
                0 <= i < PAGE_TABLE_ENTRY as int ==> #[trigger] r.1@.value().0@[i]@@ == 0,
    {
        let (ptr, Tracked(prov), Tracked(dealloc)) = DEKO_FRAME_ALLOCATOR.0.alloc(
            PAGE_SIZE as usize,
            PAGE_SIZE as usize,
        );
        // lack proof that the ptr is within the physmap range (how should we do this?)
        let paddr = PhysAddr::from(ptr);
        let vaddr = ms.phys_to_virt(paddr);  // this is problematic.

        let pptr = DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData));

        (pptr, Tracked::assume_new(), paddr)
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn update_entry_by_ptr(
        self_ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut DekoPointsTo<Self>>,
        i: usize,
        value: PageTableEntry,
    ) -> (t: PageTableEntry)
        requires
            0 <= (i as int) < old(perm).value().0@.len(),
            old(perm).wf(),
            old(perm).pptr() == self_ptr@,
            old(perm).is_init(),
            value.wf(),
        ensures
            old(perm).value().0@.index(i as int) == t,
            perm.value().0@.index(i as int) == value,
            perm.wf(),
            perm.value().0@ == old(perm).value().0@.update(i as int, value),
            perm.pptr() == self_ptr@,
            perm.is_init(),
    {
        core::mem::replace(
            unsafe {
                &mut *((self_ptr.0.addr() + i * core::mem::size_of::<
                    PageTableEntry,
                >()) as *mut PageTableEntry)
            },
            value,
        )
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
            // pte_perm.value().is_present_pte_spec(),
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
        let vaddr = mapping_space.phys_to_virt(paddr);  // note this.

        DekoPPtr(vstd::simple_pptr::PPtr(vaddr.0 as usize, core::marker::PhantomData))
    }

    /// Allocates or returns an existing 4KB page table entry for the specified virtual address.
    ///
    /// This function is the primary entry point for ensuring that a 4KB page table entry (PTE)
    /// exists for a given virtual address. It performs a hierarchical allocation strategy by
    /// walking the page table from the root level down to the 4KB level (level 0), creating
    /// intermediate page table levels as needed.
    ///
    /// # Overview
    ///
    /// The x86-64 page table hierarchy consists of 4 levels:
    /// - **Level 3 (PML4)**: Page Map Level 4 - Root level
    /// - **Level 2 (PDPT)**: Page Directory Pointer Table
    /// - **Level 1 (PDT)**: Page Directory Table
    /// - **Level 0 (PT)**: Page Table - Contains 4KB page entries
    ///
    /// This function ensures a complete translation path exists from the root to level 0 for
    /// the specified virtual address, allocating any missing intermediate levels.
    ///
    /// # Allocation Strategy
    ///
    /// 1. **Walk Phase**: First walks the existing page table structure to determine the
    ///    deepest level that already has a valid entry for the virtual address
    /// 2. **Allocation Phase**: Based on the walk result, allocates missing levels:
    ///    - If level 3 mapping found → allocate levels 2, 1, 0
    ///    - If level 2 mapping found → allocate levels 1, 0
    ///    - If level 1 mapping found → allocate level 0
    ///    - If level 0 mapping found → return existing mapping
    ///
    /// # Example Usage
    ///
    /// ```rust,ignore
    /// // Allocate PTE for virtual address 0x400000 (4MB mark)
    /// let vaddr = VirtAddr::new(0x400000);
    /// let mapping = Page::allocate_pte_4k(
    ///     pml4_page,
    ///     Tracked(&mut pgtable_perm),
    ///     vaddr,
    ///     &mapping_space,
    ///     private_bit,
    ///     shared_bit
    /// );
    ///
    /// // Result is guaranteed to be Level0 mapping
    /// match mapping {
    ///     Mapping::Level0(page_table, pte_index) => {
    ///         // Can now safely access/modify the PTE at page_table[pte_index]
    ///         // for virtual address 0x400000
    ///     }
    ///     _ => unreachable!(), // Never happens due to postcondition
    /// }
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
        broadcast use PageTablePath::lemma_path_take_fact;
        broadcast use PageTablePath::lemma_drop_last;

        let req_mapping = Self::walk(page, Tracked(perm), vaddr, ms, private_bit, shared_bit);

        proof {
            perm.lemma_walk_ensures_consistent_mapping(vaddr, req_mapping);
        }

        match req_mapping.level() {
            3 => Self::allocate_pte_lvl3(
                req_mapping,
                Tracked(perm),
                vaddr,
                ms,
                private_bit,
                shared_bit,
                false,
            ),
            2 => Self::allocate_pte_lvl2(
                req_mapping,
                Tracked(perm),
                vaddr,
                ms,
                private_bit,
                shared_bit,
                false,
            ),
            1 => Self::allocate_pte_lvl1(
                req_mapping,
                Tracked(perm),
                vaddr,
                ms,
                private_bit,
                shared_bit,
                false,
            ),
            0 => req_mapping,
            _ => {
                proof {
                    assert(false);  // by precondition.
                }
                crate::die("Invalid mapping level");
            },
        }
    }

    #[verifier::spinoff_prover]
    pub fn allocate_pte_lvl3(
        mapping: Mapping,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> (r: Mapping)
        requires
            old(perm).allocate_pte_lvl3_requires(mapping, vaddr, ms, private_bit, shared_bit, huge),
        ensures
            old(perm).allocate_pte_lvl3_ensures(vaddr, private_bit, shared_bit, huge, r, perm),
    {
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use lemma_index_at_level_spec_lt_page_entry_num;
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let Mapping::Level3(page, idx) = mapping else {
            proof {
                assert(false);  // by precondition.
            }
            crate::die("Expected Level3 mapping");
        };
        // Temporary borrow.
        //
        // This is to bypass Rust's borrow checker which forbids us
        // from creating a long-lived immutable borrow while borrowing
        // again as mutatable later.
        {
            let tracked page_perm = &perm.pgtable_perm;
            let (entry, Tracked(entry_perm)) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);
            if PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) {
                // Why don't we just continue the allocation here?
                //
                // The reason for that is a little bit subtle but important:
                // this function is invoked by `allocate_pte_4k(2m)` after
                // the walk phase which means that if the higher level's
                // entry is already present, then it must have been
                // validated as HUGE/unpresent.
                //
                // This case therefore exludes the unpresent case and
                // it must be huge so if we continue the allocation
                // here, we would accidentally overwrite a huge page.
                //
                // This also prevents us from accidentally modifying
                // the self-mapped page table entry as it must be present.
                return Mapping::Level3(page, idx);
            }
        }

        // Now we allocate a new page and start to insert it.
        let (new_page, Tracked(new_page_perm), paddr) = Page::alloc_new(ms);
        if core::intrinsics::unlikely(new_page.addr() == 0 || paddr.0 == 0) {
            // Heap does not start with 0 so use 0 to indicate OOM
            // is fine; but should we indicate something else here
            // or just die?
            crate::die("Out of memory");
        }
        let flags = PteFlags::writeable();
        let new_pte_value = PageTableEntry(
            PhysAddr(make_private_address(paddr.0, private_bit, shared_bit) | flags.bits() as u64),
        );
        let mapping = Mapping::Level2(new_page, index_at_level::<2>(vaddr));

        proof {
            // The below proof is ugly because we have to
            // manually inline everything to convince
            // bit vector. This can be wrapped into macros.
            //
            // FIXME: Into macro.
            let p = 1u64 << 0;
            let w = 1u64 << 1;
            let u = 1u64 << 2;
            let a = 1u64 << 5;
            let d = 1u64 << 6;
            let h = 1u64 << 7;
            let g = 1u64 << 8;
            let nx = 1u64 << 63;
            let all = p | w | u | a | d | h | g | nx;

            let writeable_bits = p | u | w | a | d;
            assert(flags.bits() & all == flags.bits()) by {
                assert(flags.bits() == writeable_bits & all);

                assert((writeable_bits & all) & all == (writeable_bits & all)) by (bit_vector)
                    requires
                        writeable_bits == (1u64 << 0) | (1u64 << 2) | (1u64 << 1) | (1u64 << 5) | (
                        1u64 << 6),
                        all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6)
                            | (1u64 << 7) | (1u64 << 8) | (1u64 << 63),
                ;
            }
            assert(new_pte_value.is_present_pte_spec() && !new_pte_value.is_huge_pte_spec()) by {
                assert(flags@ == from_bits(writeable_bits & all));

                assert(flags@ =~= Set::new(|p: Pte| p.bit() & (writeable_bits & all) != 0));
                assert(flags@.contains(Pte::PRESENT) && !flags@.contains(Pte::HUGE)) by {
                    assert(Pte::PRESENT.bit() == p && Pte::HUGE.bit() == h);
                    assert((p & (writeable_bits & all) != 0) && (h & (writeable_bits & all) == 0))
                        by (bit_vector)
                        requires
                            writeable_bits == (1u64 << 0) | (1u64 << 2) | (1u64 << 1) | (1u64 << 5)
                                | (1u64 << 6),
                            p == 1u64 << 0,
                            h == 1u64 << 7,
                            all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64
                                << 6) | (1u64 << 7) | (1u64 << 8) | (1u64 << 63),
                    ;
                }

                lemma_private_bit_non_interfering(private_bit, shared_bit, paddr@, flags);
            }

            let paddr_recovered = new_pte_value.address_spec(private_bit, shared_bit);
            assert(ms.kernel.in_range_spec(paddr_recovered) || ms.physmap.in_range_spec(
                paddr_recovered,
            )) by {
                assert(ms.kernel.in_range_spec(paddr) || ms.physmap.in_range_spec(paddr));

                lemma_private_addr_in_range(
                    paddr,
                    new_pte_value,
                    flags,
                    ms,
                    private_bit,
                    shared_bit,
                );
            }
        }

        // Update the entry.
        Page::update_entry_by_ptr(page, Tracked(&mut perm.pgtable_perm), idx, new_pte_value);
        proof {
            // TASK: PROVE THIS. ADJUST ANYTHING THAT NEEDS MODIFICATION.
            assume(perm.allocate_pte_lvl2_requires(
                mapping,
                vaddr,
                ms,
                private_bit,
                shared_bit,
                huge,
            ));
        }

        Page::allocate_pte_lvl2(mapping, Tracked(perm), vaddr, ms, private_bit, shared_bit, huge)
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub fn allocate_pte_lvl2(
        mapping: Mapping,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> (r: Mapping)
        requires
            old(perm).allocate_pte_lvl2_requires(mapping, vaddr, ms, private_bit, shared_bit, huge),
        ensures
            old(perm).allocate_pte_lvl2_ensures(vaddr, private_bit, shared_bit, huge, r, perm),
    {
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use lemma_index_at_level_spec_lt_page_entry_num;
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let Mapping::Level2(page, idx) = mapping else {
            proof {
                assert(false);  // by precondition.
            }

            crate::die("Expected Level2 mapping");
        };

        let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 2);
        {
            let tracked this_page_perm = &perm.storage.tracked_borrow(
                path.drop_last(),
            ).this_page_perm;
            let (entry, Tracked(entry_perm)) = page.borrow(Tracked(this_page_perm)).0.index_as_ptr(
                idx,
            );
            if PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) || huge {
                return Mapping::Level2(page, idx);
            }
        }

        let (new_page, Tracked(new_page_perm), paddr) = Page::alloc_new(ms);
        if new_page.addr() == 0 || paddr.0 == 0 {
            // Heap does not start with 0 so use 0 to indicate OOM
            // is fine; but should we indicate something else here
            // or just die?
            crate::die("Out of memory");
        }
        let flags = PteFlags::writeable();
        let new_pte_value = PageTableEntry(
            PhysAddr(make_private_address(paddr.0, private_bit, shared_bit) | flags.bits() as u64),
        );
        let mapping = Mapping::Level1(new_page, index_at_level::<1>(vaddr));
        let tracked mut page_perm = perm.storage.tracked_remove(path.drop_last());  // we remove and then re-insert later.

        // Update the entry.
        Page::update_entry_by_ptr(page, Tracked(&mut page_perm.this_page_perm), idx, new_pte_value);
        let (entry, Tracked(entry_perm)) = page.borrow(
            Tracked(&page_perm.this_page_perm),
        ).0.index_as_ptr(idx);

        Page::allocate_pte_lvl1(mapping, Tracked(perm), vaddr, ms, private_bit, shared_bit, huge)
    }

    #[verifier::spinoff_prover]
    #[verifier::external_body]
    pub fn allocate_pte_lvl1(
        mapping: Mapping,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> (r: Mapping)
        requires
            old(perm).allocate_pte_lvl1_requires(mapping, vaddr, ms, private_bit, shared_bit, huge),
        ensures
            old(perm).allocate_pte_lvl1_ensures(vaddr, private_bit, shared_bit, huge, r, perm),
    {
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let Mapping::Level1(page, idx) = mapping else {
            proof {
                assert(false);  // by precondition.
            }

            crate::die("Expected Level1 mapping");
        };

        let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 1);

        {
            let tracked this_page_perm = &perm.storage.tracked_borrow(
                path.drop_last(),
            ).this_page_perm;
            let (entry, Tracked(entry_perm)) = page.borrow(Tracked(this_page_perm)).0.index_as_ptr(
                idx,
            );
            if PageTableEntry::is_present_pte(entry, Tracked(&entry_perm)) || huge {
                return Mapping::Level1(page, idx);
            }
        }
        // Now we allocate a new page and start to insert it.
        let (new_page, Tracked(new_page_perm), paddr) = Page::alloc_new(ms);
        if core::intrinsics::unlikely(new_page.addr() == 0 || paddr.0 == 0) {
            // Heap does not start with 0 so use 0 to indicate OOM
            // is fine; but should we indicate something else here
            // or just die?
            crate::die("Out of memory");
        }
        let flags = PteFlags::writeable();
        let new_pte_value = PageTableEntry(
            PhysAddr(make_private_address(paddr.0, private_bit, shared_bit) | flags.bits() as u64),
        );

        Page::update_entry_by_ptr(page, Tracked::assume_new(), idx, new_pte_value);

        // Done
        Mapping::Level0(new_page, index_at_level::<0>(vaddr))
    }

    #[verifier::spinoff_prover]
    #[inline]
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
        Mapping::Level0(page, index_at_level::<0>(vaddr))
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
        let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 2);
        let ghost path_norm = path.normalize();
        let tracked page_perm = if path_norm.len() == 0 {
            &perm.pgtable_perm
        } else {
            &perm.storage.tracked_borrow(path_norm).this_page_perm
        };

        let (entry, Tracked(entry_perm)) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);
        if !PageTableEntry::is_valid_pte(entry, Tracked(entry_perm)) {
            Mapping::Level1(page, idx)
        } else {
            proof {
                let next_path = PageTablePath::from_vaddr_at_level(vaddr, 1);
                let paddr = entry_perm.value().address_spec(private_bit, shared_bit);
                reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);

                if path_norm.len() == 0 {
                    if idx == RECURSIVE_INDEX as usize {
                        assert(next_path.normalize() == path![]);
                    } else {
                        assert(next_path.normalize() == path![idx as int]);
                        assert(perm.storage[path![idx as int]].pte_perm == entry_perm.value());
                    }
                } else {
                    assert(next_path.normalize().drop_last() == path_norm);
                    assert(next_path.normalize().len() > 1);
                    assert(perm.storage[next_path.normalize()].pte_perm == entry_perm.value());
                }
            }

            let next_page = Page::from_entry(
                entry,
                Tracked(entry_perm),
                &ms,
                private_bit,
                shared_bit,
            );
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
        let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 3);
        let ghost path_norm = path.normalize();
        let tracked page_perm = if path_norm.len() == 0 {
            &perm.pgtable_perm
        } else {
            &perm.storage.tracked_borrow(path_norm).this_page_perm
        };

        let (entry, Tracked(entry_perm)) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);
        if !PageTableEntry::is_valid_pte(entry, Tracked(entry_perm)) {
            Mapping::Level2(page, idx)
        } else {
            proof {
                let next_path = PageTablePath::from_vaddr_at_level(vaddr, 2);
                let paddr = entry_perm.value().address_spec(private_bit, shared_bit);
                reveal_with_fuel(PageTablePath::remove_recursive_prefix, 3);

                if path_norm.len() == 0 {
                    if idx == RECURSIVE_INDEX as usize {
                        assert(next_path.normalize() == path![]);
                    } else {
                        assert(next_path.normalize() == path![idx as int]);
                        assert(perm.storage[path![idx as int]].pte_perm == entry_perm.value());
                    }
                } else {
                    assert(next_path.is_normalized());
                    assert(next_path.drop_last() == path_norm);
                    assert(next_path.len() > 1);
                    assert(perm.storage[next_path].pte_perm == entry_perm.value());
                }
            }
            let next_page = Page::from_entry(
                entry,
                Tracked(entry_perm),
                &ms,
                private_bit,
                shared_bit,
            );
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
        let tracked page_perm = &perm.pgtable_perm;

        let (entry, Tracked(entry_perm)) = page.borrow(Tracked(page_perm)).0.index_as_ptr(idx);
        if !PageTableEntry::is_valid_pte(entry, Tracked(entry_perm)) {
            // We hit the last level and the entry is not valid, so we return
            // the Level3 mapping.
            Mapping::Level3(page, idx)
        } else {
            proof {
                let path = PageTablePath::from_vaddr_at_level(vaddr, 3);
                assert(path == path![idx as int]);
                reveal_with_fuel(PageTablePath::remove_recursive_prefix, 2);
            }

            let next_page = Page::from_entry(
                entry,
                Tracked(entry_perm),
                &ms,
                private_bit,
                shared_bit,
            );

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
    pub fn virt_to_frame(
        vaddr: VirtAddr,
        private_bit: u64,
        Tracked(pgtable_perm): Tracked<&PageTablePermission>,
    ) -> (r: Option<PageFrame>)
        requires
            vaddr.wf(),
            pgtable_perm.wf(),
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

            pgtable_perm.lemma_pte_of_vaddr_cancels_with_self_mapping(vaddr);

            // ==== for preconditions ==== //
            assert(pml4e_perm_path == path![493, 493, 493, 493]);
            assert(pdpe_perm_path.take(3) == path![493, 493, 493]);
            assert(pde_perm_path.take(2) == path![493, 493]);
            assert(pte_perm_path.take(1) == path![493]);
            // =========================== //

            pgtable_perm.lemma_pml4e_always_mapped(pml4e_addr);
            pgtable_perm.lemma_pte_addr_same_as_vaddr_each_level(vaddr);

            pgtable_perm.lemma_pte_of_vaddr_shares_prefix(pdpe_addr, pml4e_addr);
            pgtable_perm.lemma_pte_of_vaddr_shares_prefix(pde_addr, pdpe_addr);
            pgtable_perm.lemma_pte_of_vaddr_shares_prefix(pte_addr, pde_addr);
            pgtable_perm.lemma_pte_of_vaddr_shares_prefix(vaddr, pte_addr);

            reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);
        }

        let (pml4e, Tracked(pml4e_perm)) = PageTableEntry::read_pte(
            pml4e_addr,
            Tracked(pgtable_perm),
        );

        if !PageTableEntry::is_present_pte(pml4e, Tracked(pml4e_perm))
            || PageTableEntry::is_huge_pte(pml4e, Tracked(pml4e_perm)) {
            return None;
        }
        let (pdpe, Tracked(pdpe_perm)) = PageTableEntry::read_pte(pdpe_addr, Tracked(pgtable_perm));
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
            pgtable_perm.lemma_pdpe_present_can_read_pde(pdpe_addr, pde_addr);
        }
        let (pde, Tracked(pde_perm)) = PageTableEntry::read_pte(pde_addr, Tracked(pgtable_perm));
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
            pgtable_perm.lemma_pde_present_can_read_pte(pde_addr, pte_addr);
        }
        let (pte, Tracked(pte_perm)) = PageTableEntry::read_pte(pte_addr, Tracked(pgtable_perm));
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
        page: DekoPPtr<Self>,
        Tracked(perm): Tracked<&PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> (r: Mapping)
        requires
            perm.walk_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            perm.walk_ensures(vaddr, r),
    {
        Self::walk_addr_lvl3(page, Tracked(perm), vaddr, ms, private_bit, shared_bit)
    }

    /// Split a huge page (2MB ONLY) into 4KB pages. So the parent page table must be at level 1.
    #[verifier::spinoff_prover]
    fn do_split_page_into_4k(
        vaddr: VirtAddr,
        page: DekoPPtr<Page>,
        idx: usize,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        Tracked(perm): Tracked<&mut PageTablePermission>,
    )
        requires
            old(perm).do_split_page_into_4k_requires(page, idx, ms, private_bit, shared_bit, vaddr),
        ensures
            old(perm).do_split_page_into_4k_ensures(page, idx, vaddr, perm),
    {
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PageTablePath::lemma_page_table_path_drop_last_implies;
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 1);
        let ghost parent_path = path.drop_last().normalize();
        let tracked this_page_perm = if parent_path.len() == 0 {
            &perm.pgtable_perm
        } else {
            &perm.storage.tracked_borrow(parent_path).this_page_perm
        };

        let (entry, Tracked(entry_perm)) = page.borrow(Tracked(this_page_perm)).0.index_as_ptr(idx);

        // LATER REMOVE THIS DUE TO precondition.
        if core::intrinsics::unlikely(!PageTableEntry::is_huge_pte(entry, Tracked(entry_perm))) {
            proof {
                assert(false);  // neeed to ensure this.
            }
            crate::die("Expected huge page");
        }
        let addr_2m = entry.borrow(Tracked(entry_perm)).address(private_bit, shared_bit);
        let mut flags = PteFlags::from_bits_truncate(entry.borrow(Tracked(entry_perm)).0.0);
        let (new_page, Tracked(new_page_perm), paddr) = Page::alloc_new(ms);
        flags.remove(HUGE);

        proof {
            assert(flags.bits() & Pte_ALL_BITS == flags.bits()) by {
                admit();
            }
        }

        // Populate the new page.
        // Perhaps we can extract this into a helper function and hide.
        let mut cur = 0usize;
        while cur < PAGE_TABLE_ENTRY
            invariant
                cur <= PAGE_TABLE_ENTRY,
                addr_2m@ + PAGE_TABLE_ENTRY * PAGE_SIZE <= 0x000f_ffff_ffff_f000,
                new_page_perm.value().0@.len() as usize == PAGE_TABLE_ENTRY,
                new_page_perm.wf(),
                new_page_perm.pptr() == new_page@,
                new_page_perm.is_init(),
                flags.wf(),
            decreases PAGE_TABLE_ENTRY - cur,
        {
            let addr_4k = addr_2m.0 + cur as u64 * PAGE_SIZE;
            let new_pte_value = PageTableEntry(
                PhysAddr(
                    make_private_address(addr_4k, private_bit, shared_bit) | flags.bits() as u64,
                ),
            );
            Page::update_entry_by_ptr(new_page, Tracked(&mut new_page_perm), cur, new_pte_value);

            cur += 1;
        }

        let new_pte_value = PageTableEntry(
            PhysAddr(make_private_address(paddr.0, private_bit, shared_bit) | flags.bits() as u64),
        );

        proof {
            assume(!flags.contains(HUGE));  // delayed to bit proofs.
            lemma_private_bit_non_interfering(private_bit, shared_bit, paddr.0, flags);
            assert(!new_pte_value.is_huge_pte_spec());
        }

        // Creating `if-else` branch here is to make verification happy.
        //
        // We cannot just obtain a &mut DekoPointsTo<Page> as Verus will complain about returning
        // &mut T from a borrowed context (as branches are involved).
        //
        // This must be circumvented by case-splitting the two scenarios in `exec` mode.
        if index_at_level::<2>(vaddr) == RECURSIVE_INDEX as usize && index_at_level::<3>(vaddr)
            == RECURSIVE_INDEX as usize {
            proof {
                assert(parent_path.len() == 0) by {
                    reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);
                }
            }

            Page::update_entry_by_ptr(page, Tracked(&mut perm.pgtable_perm), idx, new_pte_value);
        } else {
            let ghost path_norm = path.normalize();

            proof {
                assert(parent_path.wf() && path_norm.len() != 1 && path_norm != parent_path
                    && path_norm.wf() && path_norm.is_normalized() && path_norm
                    != path![RECURSIVE_INDEX as int]) by {
                    reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);

                    assert(path.drop_last()@[0] == index_at_level_spec(3, vaddr) as int);
                    assert(path.drop_last()@[1] == index_at_level_spec(2, vaddr) as int);
                }
            }
            let tracked mut page_perm = perm.storage.tracked_remove(parent_path);  // we remove and then re-insert later.
            Page::update_entry_by_ptr(
                page,
                Tracked(&mut page_perm.this_page_perm),
                idx,
                new_pte_value,
            );

            proof {
                let tracked new_page_perm = PagePermission {
                    pte_perm: new_pte_value,
                    this_page_perm: new_page_perm,
                };

                perm.storage.tracked_insert(parent_path, page_perm);
                perm.storage.tracked_insert(path_norm, new_page_perm);
                lemma_private_address_transformation_is_invertible(
                    private_bit,
                    shared_bit,
                    new_pte_value,
                    paddr.0,
                    flags,
                );
                assert(forall|i: int|
                    0 <= i < PAGE_TABLE_ENTRY as int && i != idx as int ==> old(
                        perm,
                    ).storage[parent_path].this_page_perm.value().0@[i]
                        == perm.storage[parent_path].this_page_perm.value().0@[i]);

                assert(perm.vaddr_based_wf()) by {
                    // Reasoning about this gets triciky as we need to re-construct the
                    // new_page and its children's relationship; but we do so by directing
                    // "splitting" the address from 2m regions but the permission model
                    // is not fully aware of this operation.
                    //
                    // FIXME: For now we just admit this and revisit later.
                    admit();
                }
            }
        }

        flush_tlb();
    }

    // should we add vaddr as ghost param?
    fn split_page_into_4k(
        vaddr: VirtAddr,
        mapping: Mapping,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        Tracked(perm): Tracked<&mut PageTablePermission>,
    )
        requires
            old(perm).split_page_into_4k_requires(mapping, ms, private_bit, shared_bit, vaddr),
        ensures
            old(perm).split_page_into_4k_ensures(vaddr, perm),
    {
        match mapping {
            Mapping::Level0(_, _) => {},
            Mapping::Level1(page, idx) => {
                Page::do_split_page_into_4k(
                    vaddr,
                    page,
                    idx,
                    ms,
                    private_bit,
                    shared_bit,
                    Tracked(perm),
                );
            },
            _ => {
                proof {
                    assert(false);  // by precondition.
                }
                crate::die("Expected Level1 mapping");
            },
        }
    }

    /// Sets a given page (4KB) as shared.
    #[verifier::external_body]
    pub fn set_shared_4k(
        page: DekoPPtr<Self>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    )
        requires
            old(perm).set_shared_4k_requires(page, vaddr, ms, private_bit, shared_bit),
        ensures
            old(perm).set_shared_4k_ensures(vaddr, private_bit, shared_bit, perm),
    {
        let mapping = Page::walk(page, Tracked(perm), vaddr, ms, private_bit, shared_bit);
        Page::split_page_into_4k(vaddr, mapping, ms, private_bit, shared_bit, Tracked(perm));

        // After splitting we need to walk again to get the Level0 mapping.
        let Mapping::Level0(page, idx) = Page::walk(
            page,
            Tracked(perm),
            vaddr,
            ms,
            private_bit,
            shared_bit,
        ) else {
            proof {
                assert(false);  // by precondition.
            }
            crate::die("Expected Level0 mapping");
        };

        // set shared. todo.
        let (entry, Tracked(entry_perm)) = page.borrow(Tracked::assume_new()).0.index_as_ptr(idx);  // TOOD: fix tracked.
        let pte = entry.borrow(Tracked(&entry_perm)).0.0;
        let new_pte_value = PageTableEntry(
            PhysAddr(make_shared_address(pte, private_bit, shared_bit)),
        );
        Page::update_entry_by_ptr(page, Tracked::assume_new(), idx, new_pte_value);
    }

    /// Maps _multiple_ pages in the given virtual address range to the given physical address.
    #[verifier::spinoff_prover]
    pub fn map_page_multiple(
        page: DekoPPtr<Page>,
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
        vaddr: VaddrRange,
        paddr: PhysAddr,
        flags: PteFlags,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    )
        requires
            old(pgtable_perm).map_page_multiple_requires(
                page,
                vaddr,
                paddr,
                ms,
                flags,
                private_bit,
                shared_bit,
            ),
        ensures
            old(pgtable_perm).map_page_multiple_ensures(
                vaddr,
                paddr,
                flags,
                private_bit,
                shared_bit,
                pgtable_perm,
            ),
    {
        let mut i = 0;
        let len = (vaddr.end.0 - vaddr.start.0) / PAGE_SIZE;

        while i < len
            invariant
                i <= len,
                len == (vaddr.end@ - vaddr.start@) / PAGE_SIZE as int,
                vaddr.wf(),
                flags.wf(),
                flags.bits() & Pte_ALL_BITS == flags.bits(),
                ms.wf(),
                ms == pgtable_perm.mapping_space,
                private_bit == pgtable_perm.private_bit,
                shared_bit == pgtable_perm.shared_bit,
                page.addr() == pgtable_perm.pgtable_perm.pptr().addr(),
                bit_not_overlapping(private_bit),
                bit_not_overlapping(shared_bit),
                bit_not_in_addr_region(private_bit),
                bit_not_in_addr_region(shared_bit),
                pgtable_perm.wf(),
                vaddr.start@ % PAGE_SIZE == 0,
                vaddr.end@ % PAGE_SIZE == 0,
                vaddr.end@ > vaddr.start@,
                vaddr.end@ <= VADDR_LOWER_MASK || vaddr.start@ >= VADDR_UPPER_MASK,
                paddr@ % PAGE_SIZE == 0,
                paddr@ + (vaddr.end@ - vaddr.start@) < 0x000f_ffff_ffff_f000,
                PAGE_SIZE == 0x1000,
                0 < i <= len ==> pgtable_perm.mapped_region(
                    vaddr.start..VirtAddr((vaddr.start@ + i * PAGE_SIZE) as u64),
                ),
            decreases len - i,
        {
            let curr_vaddr = VirtAddr(vaddr.start.0 + i * PAGE_SIZE);
            let curr_paddr = PhysAddr(paddr.0 + i * PAGE_SIZE);

            proof {
                assert(curr_vaddr.wf());
                // prove: pgtable_perm.walk_addr_lvl3_requires
            }

            assume(pgtable_perm.map_page_4k_requires(
                page,
                curr_vaddr,
                curr_paddr,
                ms,
                flags,
                private_bit,
                shared_bit,
            ));

            // Need to add something explicit about the before and after-state of
            // pgtable_perm to ensure that we know that mapped pages are preserved.
            // otherwise verus has no idea that previous pages are still mapped.
            Page::map_page_4k(
                page,
                Tracked(pgtable_perm),
                curr_vaddr,
                curr_paddr,
                ms,
                flags.clone(),
                private_bit,
                shared_bit,
            );

            // TODO: FIX ME LATER.
            assume(pgtable_perm.mapped_region(
                vaddr.start..VirtAddr((vaddr.start@ + (i + 1) * PAGE_SIZE) as u64),
            ));

            i += 1;
        }

    }

    /// Maps a single 4KB page at the given virtual address to the given physical address
    #[verifier::spinoff_prover]
    pub fn map_page_4k(
        page: DekoPPtr<Page>,
        Tracked(perm): Tracked<&mut PageTablePermission>,
        vaddr: VirtAddr,
        paddr: PhysAddr,  // <- this implicitly creates a "permission" out of nowhere. Is that okay?
        /* Tracked(mapped_page_perm): Tracked<PagePermission> */
        ms: &MappingSpace,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    )
        requires
            old(perm).map_page_4k_requires(page, vaddr, paddr, ms, flags, private_bit, shared_bit),
        ensures
            old(perm).map_page_4k_ensures(vaddr, paddr, flags, private_bit, shared_bit, perm),
    {
        broadcast use PteFlags::lemma_from_bits_single;
        broadcast use PteFlags::lemma_each_bits_is_valid;
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;
        // Allocate a page for us.

        let mapping = Page::allocate_pte_4k(
            page,
            Tracked(perm),
            vaddr,
            ms,
            private_bit,
            shared_bit,
        );

        let Mapping::Level0(page, idx) = mapping else {
            crate::die("Expected Level0 mapping");
        };

        let new_pte_value = PageTableEntry(
            PhysAddr(make_private_address(paddr.0, private_bit, shared_bit) | flags.bits() as u64),
        );
        let ghost path = PageTablePath::from_vaddr_at_level(vaddr, 0);
        let ghost parent_path = path.drop_last().normalize();

        proof {
            reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);
            assert(new_pte_value.address_spec(private_bit, shared_bit) == paddr) by {
                lemma_private_address_transformation_is_invertible(
                    private_bit,
                    shared_bit,
                    new_pte_value,
                    paddr.0,
                    flags,
                );
            }

            assert(path.wf() && parent_path.wf() && path.is_normalized()
                && parent_path.is_normalized());
            assert(path.len() == 4 && parent_path.len() == 3);
            assert(path != path![RECURSIVE_INDEX as int]);
            assert(parent_path != path![RECURSIVE_INDEX as int]);
        }

        let tracked perm_before = &*perm;
        let tracked mut page_perm = perm.storage.tracked_remove(parent_path);  // we remove and then re-insert later.
        Page::update_entry_by_ptr(page, Tracked(&mut page_perm.this_page_perm), idx, new_pte_value);
        proof {
            page_is_aligned();

            perm.storage.tracked_insert(parent_path, page_perm);
            perm.storage.tracked_insert(
                path,
                PagePermission {
                    pte_perm: new_pte_value,
                    this_page_perm: DekoPointsTo::any_init(
                        true,
                    ),  // TODO: Fix this later.
                },
            );

            assert(perm_before.vaddr_based_wf());
            assert forall|child_path: PageTablePath|
                #![trigger perm.storage.contains_key(child_path)]
                #![trigger perm.storage.contains_key(child_path.drop_last())]
                perm.storage.contains_key(child_path) && child_path.len() > 1 && child_path
                    != path implies {
                let parent_path = child_path.drop_last();
                let child_index = child_path@[child_path.len() - 1];

                perm.parent_child_consistency_spec(
                    child_path,
                    parent_path,
                    child_index,
                    perm.storage[child_path],
                    perm.storage[parent_path],
                )
            } by {
                if child_path != path {
                    if child_path.drop_last() == path.drop_last() {
                        assert(child_path@[child_path.len() - 1] != idx as int) by {
                            if (child_path@[child_path.len() - 1] == idx as int) {
                                assert(child_path == path);
                            }
                        }
                    }
                }
            }

            assert(perm.mapped(vaddr)) by {
                admit();  // FIX later.
            };
            assume(perm.storage[path].this_page_perm.addr() == perm.mapping_space.phys_to_virt_spec(
                new_pte_value.address_spec(private_bit, shared_bit),
            )@);

        }
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
        ;
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
        let path = PageTablePath::from_vaddr(vaddr).normalize();
        let idx = (vaddr@ >> 3) & 0x1ff;  // the index inside the page.

        if path.len() == 0 {
            // resort to root.
            pgtable_perm.pgtable_perm.value().0@.index(idx as int)
        } else {
            pgtable_perm.storage[path].this_page_perm.value().0@.index(idx as int)
        }
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
            pgtable_perm.wf(),
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
    /// Indicates that a returned mapping must be valid for a given virtual address at a certain level,
    /// i.e., it is obtained from the correct path.
    #[verifier::inline]
    pub open spec fn mapping_addr_consistent(
        &self,
        ptr: DekoPPtr<Page>,
        idx: usize,
        vaddr: VirtAddr,
        lvl: u64,
    ) -> bool
        recommends
            self.wf(),
            lvl <= 3,
    {
        let path = PageTablePath::from_vaddr_at_level(vaddr, lvl as nat);

        if lvl == 3 {
            &&& self.pgtable_perm.dptr() == ptr
            &&& path@[0] == idx as int
        } else {
            let parent_path = path.drop_last().normalize();

            if parent_path.len() == 0 {
                // Parent normalized to [] - accessing PML4 via recursive mapping
                &&& self.pgtable_perm.dptr() == ptr
                &&& path@[(3 - lvl) as int] == idx as int
            } else {
                // Normal case - parent is in storage
                &&& self.storage.contains_key(parent_path)
                &&& self.storage[parent_path].this_page_perm.dptr() == ptr
                &&& path@[(3 - lvl) as int] == idx as int
            }
        }
    }

    pub open spec fn mapping_addr_valid(
        &self,
        page: DekoPPtr<Page>,
        idx: usize,
        vaddr: VirtAddr,
        lvl: u64,
    ) -> bool
        recommends
            self.wf(),
            lvl <= 3,
    {
        let path = PageTablePath::from_vaddr(vaddr);
        let pdpe = self.get_pte(path, 3);
        let pde = self.get_pte(path, 2);
        let pte = self.get_pte(path, 1);

        match lvl {
            3 => {
                &&& page == self.storage[path![493]].this_page_perm.dptr()
                &&& idx == path@[1]
            },
            2 => {
                let path0 = path@[0];

                &&& pdpe.is_valid_pte_spec()
                &&& page == self.storage[path![path0]].this_page_perm.dptr()
                &&& idx == path@[2]
            },
            1 => {
                let path0 = path@[0];
                let path1 = path@[1];

                &&& pdpe.is_valid_pte_spec()
                &&& pde.is_valid_pte_spec()
                &&& page == self.storage[path![path0, path1]].this_page_perm.dptr()
                &&& idx == path@[3]
            },
            0 => {
                let path0 = path@[0];
                let path1 = path@[1];
                let path2 = path@[2];

                &&& pdpe.is_valid_pte_spec()
                &&& pde.is_valid_pte_spec()
                &&& pte.is_valid_pte_spec()
                &&& page == self.storage[path![path0, path1, path2]].this_page_perm.dptr()
                &&& idx == path@[3]
            },
            _ => arbitrary(),
        }
    }

    /// Ensures that a new page table permission preserves core invariants
    #[verifier::inline]
    pub open spec fn preserves_pgtable_invariants(
        &self,
        new_pgtable_perm: &PageTablePermission,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& new_pgtable_perm.wf()
        &&& new_pgtable_perm.mapping_space == self.mapping_space
        &&& new_pgtable_perm.private_bit == private_bit == self.private_bit
        &&& new_pgtable_perm.shared_bit == shared_bit == self.shared_bit
        &&& new_pgtable_perm.pgtable_perm.pptr() == self.pgtable_perm.pptr()
    }

    /// Gets the PTE at the specified level for a given path.
    /// Handles recursive mapping where normalized paths become empty.
    pub open spec fn get_pte(&self, path: PageTablePath, level: nat) -> PageTableEntry
        recommends
            self.wf(),
            level <= 3,
    {
        let path_at_level = path.take((4 - level) as int);
        let norm_path = path_at_level.normalize();

        if norm_path.len() == 0 {
            // Normalized to empty → accessing PML4 directly via recursion
            // Extract the last index from unnormalized path
            let idx = path_at_level@[path_at_level.len() - 1];
            self.pgtable_perm.value().0@[idx]
        } else {
            // Normal case: look up in storage
            self.storage[norm_path].pte_perm
        }
    }

    pub open spec fn do_split_page_into_4k_requires(
        &self,
        page: DekoPPtr<Page>,
        idx: usize,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        vaddr: VirtAddr,
    ) -> bool {
        &&& self.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& vaddr.wf()
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(
            shared_bit,
        )
        // Must be a Level1 mapping.
        &&& self.mapping_addr_consistent(page, idx, vaddr, 1)
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 1).drop_last().normalize();
            let page = if path.len() == 0 {
                &self.pgtable_perm
            } else {
                &self.storage[path].this_page_perm
            };

            &&& page.value().0@.index(idx as int).is_huge_pte_spec()
            &&& page.value().0@.index(idx as int).address_spec(private_bit, shared_bit)@
                + PAGE_TABLE_ENTRY * PAGE_SIZE <= 0x000f_ffff_ffff_f000
        }
    }

    pub open spec fn do_split_page_into_4k_ensures(
        &self,
        page: DekoPPtr<Page>,
        idx: usize,
        vaddr: VirtAddr,
        new_page_permission: &PageTablePermission,
    ) -> bool {
        &&& new_page_permission.wf()
        &&& new_page_permission.mapping_space == self.mapping_space
        &&& new_page_permission.private_bit == self.private_bit
        &&& new_page_permission.shared_bit == self.shared_bit
        // todo.

    }

    pub open spec fn split_page_into_4k_requires(
        &self,
        mapping: Mapping,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        vaddr: VirtAddr,
    ) -> bool {
        &&& self.wf()
        &&& vaddr.wf()
        &&& mapping.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& match mapping {
            Mapping::Level0(page, idx) => true,
            Mapping::Level1(page, idx) => self.do_split_page_into_4k_requires(
                page,
                idx,
                ms,
                private_bit,
                shared_bit,
                vaddr,
            ),
            _ => false,
        }
    }

    pub open spec fn split_page_into_4k_ensures(
        &self,
        vaddr: VirtAddr,
        new_perm: &PageTablePermission,
    ) -> bool {
        &&& new_perm.wf()
        &&& new_perm.mapping_space == self.mapping_space
        &&& new_perm.private_bit == self.private_bit
        &&& new_perm.shared_bit == self.shared_bit
    }

    pub open spec fn set_shared_4k_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.walk_requires(page, vaddr, ms, private_bit, shared_bit)
    }

    pub open spec fn set_shared_4k_ensures(
        &self,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        new_perm: &PageTablePermission,
    ) -> bool {
        &&& new_perm.wf()
        &&& new_perm.mapping_space == self.mapping_space
        &&& new_perm.private_bit == self.private_bit
        &&& new_perm.shared_bit == self.shared_bit
        // todo.

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
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(shared_bit)
    }

    pub open spec fn allocate_pte_4k_ensures(
        &self,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        res_mapping: Mapping,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        &&& self.preserves_pgtable_invariants(
            new_pgtable_perm,
            private_bit,
            shared_bit,
        )
        // Must return a Level0 mapping ?
        &&& res_mapping matches Mapping::Level0(ptr, idx) ==> {
            new_pgtable_perm.mapping_addr_consistent(ptr, idx, vaddr, 0)
        }
    }

    pub open spec fn allocate_pte_lvl3_requires(
        &self,
        mapping: Mapping,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> bool {
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(shared_bit)
        &&& mapping.wf()
        &&& mapping matches Mapping::Level3(page_lvl3, idx) && self.mapping_addr_consistent(
            page_lvl3,
            idx,
            vaddr,
            3,
        )
    }

    pub open spec fn allocate_pte_lvl3_ensures(
        &self,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
        res_mapping: Mapping,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        &&& self.preserves_pgtable_invariants(new_pgtable_perm, private_bit, shared_bit)
        &&& res_mapping matches Mapping::Level0(ptr, idx) ==> {
            new_pgtable_perm.mapping_addr_consistent(ptr, idx, vaddr, 0)
        }
        // &&& self.allocated_mapping_result_valid(vaddr, huge, res_mapping, new_pgtable_perm)

    }

    pub open spec fn allocate_pte_lvl2_requires(
        &self,
        mapping: Mapping,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> bool {
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(shared_bit)
        &&& mapping.wf()
        &&& mapping matches Mapping::Level2(page_lvl2, idx) && self.mapping_addr_consistent(
            page_lvl2,
            idx,
            vaddr,
            2,
        )
    }

    pub open spec fn allocate_pte_lvl2_ensures(
        &self,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
        res_mapping: Mapping,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        &&& self.preserves_pgtable_invariants(new_pgtable_perm, private_bit, shared_bit)
        &&& res_mapping matches Mapping::Level0(ptr, idx) ==> {
            new_pgtable_perm.mapping_addr_consistent(ptr, idx, vaddr, 0)
        }
        // &&& self.allocated_mapping_result_valid(vaddr, huge, res_mapping, new_pgtable_perm)

    }

    pub open spec fn allocate_pte_lvl1_requires(
        &self,
        mapping: Mapping,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
    ) -> bool {
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(shared_bit)
        &&& mapping.wf()
        &&& mapping matches Mapping::Level1(page_lvl1, idx) && self.mapping_addr_consistent(
            page_lvl1,
            idx,
            vaddr,
            1,
        )
    }

    pub open spec fn allocate_pte_lvl1_ensures(
        &self,
        vaddr: VirtAddr,
        private_bit: u64,
        shared_bit: u64,
        huge: bool,
        res_mapping: Mapping,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        &&& self.preserves_pgtable_invariants(new_pgtable_perm, private_bit, shared_bit)
        &&& res_mapping matches Mapping::Level0(ptr, idx) ==> {
            new_pgtable_perm.mapping_addr_consistent(ptr, idx, vaddr, 0)
        }
    }

    pub open spec fn map_page_multiple_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr_range: VaddrRange,
        paddr: PhysAddr,
        ms: &MappingSpace,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& page.addr() == self.pgtable_perm.pptr().addr()
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(shared_bit)
        &&& flags.wf()
        &&& flags.bits() & Pte_ALL_BITS == flags.bits()
        &&& paddr.wf()
        &&& paddr@ % PAGE_SIZE == 0
        &&& paddr@ + (vaddr_range.end@ - vaddr_range.start@) < 0x000f_ffff_ffff_f000
        &&& vaddr_range.wf()
        &&& vaddr_range.start@ % PAGE_SIZE == 0
        &&& vaddr_range.end@ % PAGE_SIZE == 0
    }

    pub open spec fn map_page_multiple_ensures(
        &self,
        vaddr_range: VaddrRange,
        paddr: PhysAddr,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        &&& self.preserves_pgtable_invariants(new_pgtable_perm, private_bit, shared_bit)
        &&& new_pgtable_perm.mapped_region(vaddr_range)
    }

    pub open spec fn map_page_4k_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        ms: &MappingSpace,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.allocate_pte_4k_requires(page, vaddr, ms, private_bit, shared_bit)
        &&& bit_not_overlapping(private_bit)
        &&& bit_not_overlapping(shared_bit)
        &&& bit_not_in_addr_region(private_bit)
        &&& bit_not_in_addr_region(shared_bit)
        &&& flags.wf()
        &&& flags.bits() & Pte_ALL_BITS == flags.bits()
        &&& paddr.wf()
        &&& paddr@ % PAGE_SIZE == 0
        &&& paddr@ < 0x000f_ffff_ffff_f000
        &&& ms.kernel.in_range_spec(paddr) || ms.physmap.in_range_spec(
            paddr,
        )
        // Must be canonical path for vaddr.
        &&& {
            let path = PageTablePath::from_vaddr(vaddr);

            &&& path.is_normalized()
            &&& path.wf()
        }
    }

    pub open spec fn map_page_4k_ensures(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: PteFlags,
        private_bit: u64,
        shared_bit: u64,
        new_pgtable_perm: &PageTablePermission,
    ) -> bool {
        &&& self.preserves_pgtable_invariants(new_pgtable_perm, private_bit, shared_bit)
        &&& new_pgtable_perm.mapped(vaddr)
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
            self.wf(),
            vaddr.wf(),
    {
        self.walk_addr_lvl3_spec(vaddr)
    }

    #[verifier::inline]
    pub open spec fn walk_ensures(&self, vaddr: VirtAddr, res_mapping: Mapping) -> bool {
        &&& res_mapping == self.walk_spec(vaddr)
    }

    pub open spec fn walk_addr_lvl0_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 1);
            let norm_path = path.normalize();

            if norm_path.len() == 0 {
                // Path normalized to [] - accessing PML4 via recursive mapping
                // This happens when vaddr = [493, 493, 493, ...]
                &&& page.addr() == self.pgtable_perm.pptr().addr()
                &&& self.pgtable_perm.value().0@[RECURSIVE_INDEX as int].is_present_pte_spec()
            } else {
                // Normal case - accessing a PT from storage
                &&& self.storage.contains_key(norm_path)
                &&& page.addr() == self.storage[norm_path].this_page_perm.pptr().addr()
                &&& self.storage[norm_path].pte_perm.is_present_pte_spec()
            }
        }
    }

    pub open spec fn walk_addr_lvl0_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let idx = index_at_level_spec(0, vaddr);
        let parent_path = PageTablePath::from_vaddr_at_level(vaddr, 1);
        let norm_parent = parent_path.normalize();

        let parent = if norm_parent.len() == 0 {
            // Accessing PML4 via recursive mapping (vaddr starts with 493)
            self.pgtable_perm
        } else {
            // Normal case - accessing PDPT from storage
            self.storage[norm_parent].this_page_perm
        };

        Mapping::Level0(parent.dptr(), idx as usize)
    }

    pub open spec fn walk_addr_lvl1_requires(
        &self,
        page: DekoPPtr<Page>,
        vaddr: VirtAddr,
        ms: &MappingSpace,
        private_bit: u64,
        shared_bit: u64,
    ) -> bool {
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 2);
            let norm_path = path.normalize();

            if norm_path.len() == 0 {
                // Path normalized to [] - accessing PML4 via recursive mapping
                // This happens when vaddr = [493, 493, ...]
                &&& page.addr() == self.pgtable_perm.pptr().addr()
                &&& self.pgtable_perm.value().0@[RECURSIVE_INDEX as int].is_present_pte_spec()
            } else {
                // Normal case - accessing a PD from storage
                &&& self.storage.contains_key(norm_path)
                &&& page.addr() == self.storage[norm_path].this_page_perm.pptr().addr()
                &&& self.storage[norm_path].pte_perm.is_present_pte_spec()
            }
        }
    }

    pub open spec fn walk_addr_lvl1_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let idx = index_at_level_spec(1, vaddr);
        let parent_path = PageTablePath::from_vaddr_at_level(vaddr, 2);
        let norm_parent = parent_path.normalize();

        let parent = if norm_parent.len() == 0 {
            // Accessing PML4 via recursive mapping (vaddr starts with 493)
            self.pgtable_perm
        } else {
            // Normal case - accessing PDPT from storage
            self.storage[norm_parent].this_page_perm
        };

        let pte = parent.value().0@[idx];

        if !pte.is_valid_pte_spec() {
            Mapping::Level1(parent.dptr(), idx as usize)
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
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& {
            let path = PageTablePath::from_vaddr_at_level(vaddr, 3);
            let norm_path = path.normalize();

            if norm_path.len() == 0 {
                // Path normalized to [] - accessing PML4 via recursive mapping
                // This happens when vaddr starts with [493, ...]
                &&& page.addr() == self.pgtable_perm.pptr().addr()
                &&& self.pgtable_perm.value().0@[RECURSIVE_INDEX as int].is_present_pte_spec()
            } else {
                // Normal case - accessing a PDPT from storage
                &&& self.storage.contains_key(norm_path)
                &&& page.addr() == self.storage[norm_path].this_page_perm.pptr().addr()
                &&& self.storage[norm_path].pte_perm.is_present_pte_spec()
            }
        }
    }

    pub open spec fn walk_addr_lvl2_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf_with_perm(),
            vaddr.wf(),
    {
        let idx = index_at_level_spec(2, vaddr);
        let parent_path = PageTablePath::from_vaddr_at_level(vaddr, 3);
        let norm_parent = parent_path.normalize();

        let parent = if norm_parent.len() == 0 {
            // Accessing PML4 via recursive mapping (vaddr starts with 493)
            self.pgtable_perm
        } else {
            // Normal case - accessing PDPT from storage
            self.storage[norm_parent].this_page_perm
        };

        let pte = parent.value().0@[idx];

        if !pte.is_valid_pte_spec() {
            Mapping::Level2(parent.dptr(), idx as usize)
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
        &&& self.wf()
        &&& vaddr.wf()
        &&& ms.wf()
        &&& ms == self.mapping_space
        &&& self.private_bit == private_bit
        &&& self.shared_bit == shared_bit
        &&& page.addr() == self.pgtable_perm.pptr().addr()
    }

    pub open spec fn walk_addr_lvl3_spec(&self, vaddr: VirtAddr) -> Mapping
        recommends
            self.wf(),
            vaddr.wf(),
    {
        let path = PageTablePath::from_vaddr(vaddr);
        let idx = path@[0];

        let pml4e = self.pgtable_perm;
        let pte = pml4e.value().0@.index(idx);
        if !pte.is_valid_pte_spec() {
            Mapping::Level3(pml4e.dptr(), idx as usize)
        } else {
            self.walk_addr_lvl2_spec(vaddr)
        }
    }

    /// Checks whether all pages in the given virtual address range are mapped.
    pub open spec fn mapped_region(&self, vaddr_range: VaddrRange) -> bool
        recommends
            self.wf(),
            vaddr_range.wf(),
    {
        // We need to step by PAGE_SIZE to check each page in the range.
        forall|vaddr: VirtAddr|
            #![trigger self.mapped(vaddr)]
            vaddr_range.start@ <= vaddr@ && vaddr@ < vaddr_range.end@ && vaddr@ % PAGE_SIZE == 0
                ==> self.mapped(vaddr)
    }

    /// This spec is explicitly marked as non-inline to avoid
    /// trigger invalidation for the [`Self::mapped_region`]
    /// specification.
    pub open spec fn mapped(&self, vaddr: VirtAddr) -> bool {
        self.virt_to_frame_spec(vaddr) matches Some(_)
    }

    /// This specification works slightly differently from the walk function which
    /// returns the mapping at the lowest level if possible even if a page is not
    /// mapped at that level.
    ///
    /// However this specification function returns None if the page is not mapped
    /// at intermediate levels.
    pub open spec fn virt_to_frame_spec(&self, vaddr: VirtAddr) -> Option<PageFrame>
        recommends
            self.wf(),
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

        &&& pml4e_index_3 == pml4e_index_2 == pml4e_index_1 == pml4e_index_0
            == RECURSIVE_INDEX as int
        &&& pdpe_index_3 == pdpe_index_2 == pdpe_index_1 == RECURSIVE_INDEX as int
        &&& pde_index_3 == pde_index_2 == RECURSIVE_INDEX as int
        &&& pte_index_3 == RECURSIVE_INDEX as int
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
            self.wf(),
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
    pub proof fn lemma_pde_present_can_read_pte(&self, pde_addr: VirtAddr, pte_addr: VirtAddr)
        requires
            self.wf(),
            self.virt_to_frame_spec(pde_addr) matches Some(_),
            pde_addr.wf() && pte_addr.wf(),
            // we do not know take(1) breaks the proof.
            PageTablePath::from_vaddr(pte_addr)@.first() == 493,
            Page::get_pte_address_spec(pte_addr) == pde_addr,
            PageTableEntry::read_pte_spec(pde_addr, self).is_present_pte_spec(),
        ensures
            self.virt_to_frame_spec(pte_addr) matches Some(_),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let pte_path = PageTablePath::from_vaddr(pte_addr);
        let pde_path = PageTablePath::from_vaddr(pde_addr);

        assert(pte_path@[0] == 493);
        let a = pte_path@[1];
        let b = pte_path@[2];
        let c = pte_path@[3];

        self.lemma_pte_of_vaddr_cancels_with_self_mapping(pte_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pte_addr, pde_addr);
        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 10);  // Sometimes 5 is not enough.

        assert(pde_path == path![493, 493, a, b]);
        if a == 493 {
            assert(pte_path.take(2) == path![493, 493]);
            self.lemma_pdpe_present_can_read_pde(pde_addr, pte_addr);
        } else {
            let pte_lvl2 = self.get_pte(pte_path, 2);
            let pde_lvl1 = self.get_pte(pde_path, 1);

            assert(pte_lvl2 == self.storage[path![a]].pte_perm);
            assert(pde_lvl1 == self.storage[path![a]].pte_perm);
            assert(pte_lvl2.is_present_pte_spec());

            if pte_lvl2.is_huge_pte_spec() {
            } else {
                let pte_lvl1 = self.get_pte(pte_path, 1);
                let pde_lvl0 = self.get_pte(pde_path, 0);
                assert(pte_path.take(3).normalize() == path![a, b]);
                assert(pde_path.take(4).normalize() == path![a, b]);

                assert(pte_lvl1 == self.storage[path![a, b]].pte_perm);
                assert(pde_lvl0 == self.storage[path![a, b]].pte_perm);
                assert(pte_lvl1.is_present_pte_spec());

                if pte_lvl1.is_huge_pte_spec() {
                } else {
                    let pte_lvl0 = self.get_pte(pte_path, 0);
                    assert(pte_path.take(4).normalize() == path![a, b, c]);

                    assert(pte_lvl0 == self.storage[path![a, b, c]].pte_perm);
                    assert(path![a, b, c].drop_last() == path![a, b]);
                }
            }
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_pdpe_present_can_read_pde(&self, pdpe_addr: VirtAddr, pde_addr: VirtAddr)
        requires
            self.wf(),
            self.virt_to_frame_spec(pdpe_addr) matches Some(_),
            pdpe_addr.wf() && pde_addr.wf(),
            PageTablePath::from_vaddr(pde_addr).take(2) == path![493, 493],
            Page::get_pte_address_spec(pde_addr) == pdpe_addr,
            PageTableEntry::read_pte_spec(pdpe_addr, self).is_present_pte_spec(),
        ensures
            self.virt_to_frame_spec(pde_addr) matches Some(_),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let pde_path = PageTablePath::from_vaddr(pde_addr);
        let pdpe_path = PageTablePath::from_vaddr(pdpe_addr);

        assert(pde_path@[0] == 493);
        assert(pde_path@[1] == 493);
        let a = pde_path@[2];
        let b = pde_path@[3];

        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);
        self.lemma_pte_of_vaddr_cancels_with_self_mapping(pde_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pde_addr, pdpe_addr);

        // pdpe_addr = get_pte_address(pde_addr) = [493, 493, 493, a, b*8]
        assert(pdpe_path == path![493, 493, 493, a]);
        if a == 493 {
            // done.
        } else {
            let pte_lvl1 = self.get_pte(pde_path, 1);
            let pte_val = PageTableEntry::read_pte_spec(pdpe_addr, self);

            assert(pte_lvl1 == self.storage[path![a]].pte_perm);

            if pte_lvl1.is_huge_pte_spec() {
            } else {
                // For revealing the index.
                assert(pde_path.take(4).normalize() == path![a, b]);
                assert(pdpe_path.normalize() == path![a]);
                // For revealing child-parent relationship
                assert(path![a, b].drop_last() == path![a]);
            }
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_pml4e_present_can_read_pdpe(&self, pml4e_addr: VirtAddr, pdpe_addr: VirtAddr)
        requires
            self.wf(),
            self.virt_to_frame_spec(pml4e_addr) matches Some(_),
            pml4e_addr.wf() && pdpe_addr.wf(),
            PageTablePath::from_vaddr(pdpe_addr).take(3) == path![493, 493, 493],
            Page::get_pte_address_spec(pdpe_addr) == pml4e_addr,
            PageTableEntry::read_pte_spec(pml4e_addr, self).is_present_pte_spec(),
        ensures
            self.virt_to_frame_spec(pdpe_addr) matches Some(_),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;

        let pdpe_path = PageTablePath::from_vaddr(pdpe_addr);
        let pml4e_path = PageTablePath::from_vaddr(pml4e_addr);

        assert(pdpe_path@[0] == 493);
        assert(pdpe_path@[1] == 493);
        assert(pdpe_path@[2] == 493);
        let a = pdpe_path@[3];

        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);
        self.lemma_pte_of_vaddr_cancels_with_self_mapping(pdpe_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pdpe_addr, pml4e_addr);
        assert(pml4e_path == path![493, 493, 493, 493]);
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

    #[verifier::spinoff_prover]
    pub proof fn lemma_walk_ensures_consistent_mapping(&self, vaddr: VirtAddr, mapping: Mapping)
        requires
            self.wf(),
            vaddr.wf(),
            self.walk_ensures(vaddr, mapping),
        ensures
            match mapping {
                Mapping::Level0(ptr, idx) => self.mapping_addr_consistent(ptr, idx, vaddr, 0),
                Mapping::Level1(ptr, idx) => self.mapping_addr_consistent(ptr, idx, vaddr, 1),
                Mapping::Level2(ptr, idx) => self.mapping_addr_consistent(ptr, idx, vaddr, 2),
                Mapping::Level3(ptr, idx) => self.mapping_addr_consistent(ptr, idx, vaddr, 3),
            },
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;
        broadcast use PageTablePath::lemma_page_table_path_drop_last_implies;
        broadcast use PageTablePath::lemma_page_table_path_drop_last_normalize_exchangeable;

        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);

        match mapping {
            Mapping::Level0(ptr, idx) => {
                let path_lvl1 = PageTablePath::from_vaddr_at_level(vaddr, 1);
                let path_this = PageTablePath::from_vaddr_at_level(vaddr, 0);
                assert(path_this.drop_last() == path_lvl1);  // expose this; verus does not initiate the trigger for this. weird.
            },
            _ => {},
        }
    }

    pub open spec fn pte_addr_same_as_vaddr_each_level_spec(&self, vaddr: VirtAddr) -> bool
        recommends
            self.wf(),
            vaddr.wf(),
    {
        let pte_addr = Page::get_pte_address_spec(vaddr);
        let pde_addr = Page::get_pte_address_spec(pte_addr);
        let pdpe_addr = Page::get_pte_address_spec(pde_addr);
        let pml4_addr = Page::get_pte_address_spec(pdpe_addr);

        let vaddr_path = PageTablePath::from_vaddr(vaddr);

        // Read values from recursive addresses
        let pte_val = PageTableEntry::read_pte_spec(pte_addr, self);
        let pde_val = PageTableEntry::read_pte_spec(pde_addr, self);
        let pdpe_val = PageTableEntry::read_pte_spec(pdpe_addr, self);
        let pml4e_val = PageTableEntry::read_pte_spec(pml4_addr, self);

        // Get values from storage/pgtable_perm (handle normalization to [])
        &&& self.get_pte(vaddr_path, 3) == pml4e_val
        &&& self.get_pte(vaddr_path, 2) == pdpe_val
        &&& self.get_pte(vaddr_path, 1) == pde_val
        &&& self.get_pte(vaddr_path, 0) == pte_val
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_pte_addr_same_as_vaddr_each_level(&self, vaddr: VirtAddr)
        requires
            self.wf(),
            vaddr.wf(),
        ensures
            self.pte_addr_same_as_vaddr_each_level_spec(vaddr),
    {
        broadcast use PageTablePath::lemma_from_vaddr_at_level_makes_wf;
        broadcast use Page::lemma_get_pte_address_wf;

        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);

        self.lemma_pte_of_vaddr_cancels_with_self_mapping(vaddr);

        let pte_addr = Page::get_pte_address_spec(vaddr);
        let pde_addr = Page::get_pte_address_spec(pte_addr);
        let pdpe_addr = Page::get_pte_address_spec(pde_addr);
        let pml4_addr = Page::get_pte_address_spec(pdpe_addr);

        self.lemma_pte_of_vaddr_shares_prefix(vaddr, pte_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pte_addr, pde_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pde_addr, pdpe_addr);
        self.lemma_pte_of_vaddr_shares_prefix(pdpe_addr, pml4_addr);

        let pte_path = PageTablePath::from_vaddr(pte_addr);
        let pde_path = PageTablePath::from_vaddr(pde_addr);
        let pdpe_path = PageTablePath::from_vaddr(pdpe_addr);
        let pml4e_path = PageTablePath::from_vaddr(pml4_addr);
        let vaddr_path = PageTablePath::from_vaddr(vaddr);

        let vaddr0 = vaddr_path@[0];
        let vaddr1 = vaddr_path@[1];
        let vaddr2 = vaddr_path@[2];
        let vaddr3 = vaddr_path@[3];

        assert(path![vaddr0, vaddr1].drop_last() == path![vaddr0]);
        assert(path![vaddr0, vaddr1, vaddr2].drop_last() == path![vaddr0, vaddr1]);
        assert(path![vaddr0, vaddr1, vaddr2, vaddr3].drop_last() == path![vaddr0, vaddr1, vaddr2]);
        assert(path![vaddr1, vaddr2].drop_last() == path![vaddr1]);
        assert(path![vaddr1, vaddr2, vaddr3].drop_last() == path![vaddr1, vaddr2]);
        assert(path![vaddr2, vaddr3].drop_last() == path![vaddr2]);

        assert(pml4e_path == path![493, 493, 493, 493]);
        assert(pdpe_path == path![493, 493, 493, vaddr0]);
        assert(pde_path == path![493, 493, vaddr0, vaddr1]);
        assert(pte_path == path![493, vaddr0, vaddr1, vaddr2]);

        // need to reason about 493.
        if vaddr0 == 493 {
            if vaddr1 == 493 {
                if vaddr2 == 493 {
                } else {
                    assert(vaddr_path.take(4).normalize() == path![vaddr2, vaddr3]);
                    assert(vaddr_path.take(3).normalize() == path![vaddr2]);
                    assert(vaddr_path.take(2).normalize() == path![]);
                    assert(vaddr_path.take(1).normalize() == path![]);

                    assert(pml4e_path.normalize() == path![]);
                    assert(pdpe_path.normalize() == path![]);
                    assert(pde_path.normalize() == path![]);
                    assert(pte_path.normalize() == path![vaddr2]);
                }
            } else {
                assert(vaddr_path.take(4).normalize() == path![vaddr1, vaddr2, vaddr3]);
                assert(vaddr_path.take(3).normalize() == path![vaddr1, vaddr2]);
                assert(vaddr_path.take(2).normalize() == path![vaddr1]);
                assert(vaddr_path.take(1).normalize() == path![]);

                assert(pml4e_path.normalize() == path![]);
                assert(pdpe_path.normalize() == path![]);
                assert(pde_path.normalize() == path![vaddr1]);
                assert(pte_path.normalize() == path![vaddr1, vaddr2]);
            }
        } else {
            assert(vaddr_path.take(4).normalize() == path![vaddr0, vaddr1, vaddr2, vaddr3]);
            assert(vaddr_path.take(3).normalize() == path![vaddr0, vaddr1, vaddr2]);
            assert(vaddr_path.take(2).normalize() == path![vaddr0, vaddr1]);
            assert(vaddr_path.take(1).normalize() == path![vaddr0]);

            assert(pml4e_path.normalize() == path![]);
            assert(pdpe_path.normalize() == path![vaddr0]);
            assert(pde_path.normalize() == path![vaddr0, vaddr1]);
            assert(pte_path.normalize() == path![vaddr0, vaddr1, vaddr2]);
        }

    }

    /// **PROOF**: Proves that the PML4E for any virtual address is always mapped.
    #[verifier::spinoff_prover]
    pub proof fn lemma_pml4e_always_mapped(&self, vaddr: VirtAddr)
        requires
            self.wf(),
            vaddr.wf(),
            PageTablePath::from_vaddr(vaddr)@ == path![493, 493, 493, 493]@,
        ensures
            self.virt_to_frame_spec(vaddr) matches Some(_),
    {
        reveal_with_fuel(PageTablePath::remove_recursive_prefix, 5);

        let path = PageTablePath::from_vaddr(vaddr);
        assert(path@.take(4) == path![493, 493, 493, 493]@);
        assert(path@.take(3) == path![493, 493, 493]@);
        assert(path@.take(2) == path![493, 493]@);
        assert(path@.take(1) == path![493]@);

        assert(path![493].normalize() == path![]);
        assert(path![493, 493].normalize() == path![]);
        assert(path![493, 493, 493].normalize() == path![]);
        assert(path![493, 493, 493, 493].normalize() == path![]);
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

    // ============================================================================
    // LEVEL 1: Domain Invariants
    // ============================================================================
    /// Storage contains only normalized, non-special paths.
    /// Excludes: path![] (PML4 root) and path![493] (recursive entry).
    #[verifier::inline]
    pub open spec fn storage_domain_valid(&self) -> bool {
        forall|path: PageTablePath|
            #![trigger self.storage.contains_key(path)]
            self.storage.contains_key(path) ==> {
                &&& path.is_normalized()
                &&& path.wf()  // Implies len > 0, excludes path![]
                &&& path@ != path![RECURSIVE_INDEX as int]@
            }
    }

    // ============================================================================
    // LEVEL 2: Structural Invariants
    // ============================================================================
    /// Ensures the self-mapped recursive entry is valid.
    ///
    /// PML4[493] points back to PML4 itself, enabling recursive page table access.
    /// This is checked via `pgtable_perm`, NOT storage (since path![493] isn't stored).
    #[verifier::inline]
    pub open spec fn self_mapped(&self) -> bool {
        let pml4_page = self.pgtable_perm.value();
        let recursive_entry = pml4_page.0@[RECURSIVE_INDEX as int];
        let recursive_entry_paddr = recursive_entry.address_spec(self.private_bit, self.shared_bit);
        let recursive_entry_vaddr = self.mapping_space.phys_to_virt_spec(recursive_entry_paddr);

        // The recursive entry is present and points to PML4
        &&& recursive_entry.is_present_pte_spec()
        &&& !recursive_entry.is_huge_pte_spec()
        &&& self.mapping_space.kernel.in_range_spec(recursive_entry_paddr)
            || self.mapping_space.physmap.in_range_spec(recursive_entry_paddr)
        &&& recursive_entry_vaddr@ as usize == self.pgtable_perm.pptr().addr()
    }

    /// Validates a single path's translation.
    #[verifier::inline]
    pub open spec fn translates_address_valid(&self, path: PageTablePath) -> bool
        recommends
            path.wf(),
            path.is_normalized(),
            path@ != path![RECURSIVE_INDEX as int]@,
    {
        &&& self.storage.contains_key(
            path,
        )
        // Root level (PML4) cannot be huge pages
        &&& path.len() == 1
            ==> !self.storage[path].pte_perm.is_huge_pte_spec()
        // Entry is well-formed for its level
        &&& self.storage[path].wf_level()
        // Physical and virtual addresses are consistent
        &&& {
            let paddr = self.storage[path].pte_perm.address_spec(self.private_bit, self.shared_bit);
            let vaddr = self.mapping_space.phys_to_virt_spec(paddr);

            // Physical address is in valid range
            &&& (self.mapping_space.kernel.in_range_spec(paddr)
                || self.mapping_space.physmap.in_range_spec(
                paddr,
            ))
            // Virtual/physical mapping is consistent
            &&& self.storage[path].this_page_perm.pptr().addr() == vaddr@ as usize
        }
    }

    /// All valid paths have translations.
    #[verifier::inline]
    pub open spec fn translates_all_valid_addresses(&self) -> bool {
        forall|path: PageTablePath|
            #![trigger self.storage[path]]
            path.wf() && path.is_normalized() && path@ != path![RECURSIVE_INDEX as int]@
                ==> self.translates_address_valid(path)
    }

    // ============================================================================
    // LEVEL 3: Relational Invariants
    // ============================================================================
    /// Validates parent-child consistency.
    #[verifier::inline]
    pub open spec fn parent_child_consistency_spec(
        &self,
        child_path: PageTablePath,
        parent_path: PageTablePath,
        child_index: int,
        child: PagePermission,
        parent: PagePermission,
    ) -> bool {
        &&& self.storage.contains_key(
            parent_path,
        )
        // Child's PTE ALWAYS matches parent's page (present or not)
        &&& child.pte_perm
            == parent.this_page_perm.value().0@[child_index]
        // Additional validation ONLY if the PTE is present
        &&& child.pte_perm.is_present_pte_spec() ==> {
            let pte_phys_addr = child.pte_perm.address_spec(self.private_bit, self.shared_bit);
            let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);

            // Physical address is valid
            &&& (self.mapping_space.kernel.in_range_spec(pte_phys_addr)
                || self.mapping_space.physmap.in_range_spec(
                pte_phys_addr,
            ))
            // Virtual mapping is consistent
            &&& child.this_page_perm.pptr().addr() == vaddr@ as usize
        }
    }

    /// Unified parent-child consistency for entire hierarchy.
    #[verifier::inline]
    pub open spec fn vaddr_based_wf(&self) -> bool {
        // Check consistency between all parent-child pairs
        &&& forall|child_path: PageTablePath|
            #![trigger self.storage[child_path]]
            #![trigger self.storage[child_path.drop_last()]]
            self.storage.contains_key(child_path) && child_path.len() > 1 ==> {
                let parent_path = child_path.drop_last();
                let child_index = child_path@[child_path.len() - 1];

                self.parent_child_consistency_spec(
                    child_path,
                    parent_path,
                    child_index,
                    self.storage[child_path],
                    self.storage[parent_path],
                )
            }
            // Special case: PML4 entries (len==1) must match physical PML4 page
            // This connects storage to pgtable_perm
        &&& forall|path: PageTablePath|
            #![trigger self.storage[path]]
            self.storage.contains_key(path) && path.len() == 1 ==> {
                let pml4_page = self.pgtable_perm.value();
                let entry = self.storage[path];

                // The PTE value must match what's in the physical PML4 page
                &&& entry.pte_perm == pml4_page.0@[path@[0]]
                &&& {
                    let pte_phys_addr = entry.pte_perm.address_spec(
                        self.private_bit,
                        self.shared_bit,
                    );
                    let vaddr = self.mapping_space.phys_to_virt_spec(pte_phys_addr);

                    // Physical address is valid
                    &&& (self.mapping_space.kernel.in_range_spec(pte_phys_addr)
                        || self.mapping_space.physmap.in_range_spec(
                        pte_phys_addr,
                    ))
                    // Virtual mapping is consistent
                    &&& entry.this_page_perm.pptr().addr() == vaddr@ as usize
                }
            }
    }

    // ============================================================================
    // MASTER WELL-FORMEDNESS
    // ============================================================================
    /// Complete well-formedness of the page table structure.
    ///
    /// # Guarantees
    ///
    /// 1. **Domain Correctness**: Storage contains only valid, normalized paths
    /// 2. **Recursive Mapping**: PML4[493] correctly points to PML4 itself
    /// 3. **Individual Validity**: Each entry is well-formed with valid addresses
    /// 4. **Hierarchical Consistency**: Parent-child relationships are coherent
    /// 5. **Complete Coverage**: All valid addresses have translations.
    #[verifier::inline]
    pub open spec fn wf_with_perm(&self) -> bool {
        // Level 1: Domain restrictions
        &&& self.storage_domain_valid()
        // Level 2: Structural invariants
        &&& self.self_mapped()
        &&& self.translates_all_valid_addresses()
        // Level 3: Relational invariants
        &&& self.vaddr_based_wf()
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

    }

    /// Creates a null PagePermission with zeroed PTE and null `this_page_perm`
    /// so that we can create empty page entries to make wf happy.
    pub uninterp spec fn null() -> Self;

    pub axiom fn null_ensures()
        ensures
            ({
                let p = PagePermission::null();

                &&& p.wf_level()
                &&& !p.pte_perm.is_present_pte_spec()
                &&& forall|i: int|
                    0 <= i < PAGE_TABLE_ENTRY ==> !(#[trigger] p.this_page_perm.value().0@.index(
                        i,
                    )).is_present_pte_spec()
            }),
    ;
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

/// A mapping at a specific level in the page table hierarchy, along with its index.
/// It stores a pointer to the page table itself at that level and the index gives
/// the caller to index into the table to get the PTE.
///
/// Curious folk might wonder why don't we just return a pointer to the PTE directly?
/// This is because the pointer we return can be `mut` and we want to allow Verus
/// to reason about the _side effect_ of such a modification but unfortunately using
/// a pointer is impossible to to do so as we cannot obtain a mutable permission to
/// call [`DekoPPtr::write`]:
///
/// - Obtain it through an abstract [`vstd::seq::Seq`] that stores permissions? This
///   requires us to add more synchronization properties and unfortunately there is
///   no way to associate a [`DekoPointsTo<PageTableEntry>`] with [`Page`]'s entry.
/// - Using `external_body` to lift this restriction? This is treating and has no
///   verification value.
///
/// Verus is unfortunately not so smart to reason about pointers that might belong to
/// large arrays when treated as pointers too. For example, we cannot reason about
///
/// ```rust,ignore
/// let mut r = Array：：<u64, 512>::fill(0);
///
/// let r = r.idx_ptr(0). // It is possible to modify r[0] through r,
/// ```
///
/// TODO
///
/// - [ ] Fix mapping's definition.
/// - [ ] Make walk and allocate take input as Mapping.
/// - [ ] remove `this_page` as no longer needed.
#[derive(Clone, Copy)]
pub enum Mapping {
    Level3(DekoPPtr<Page>, usize),
    Level2(DekoPPtr<Page>, usize),
    Level1(DekoPPtr<Page>, usize),
    Level0(DekoPPtr<Page>, usize),
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
        let idx = match self {
            Mapping::Level3(_, idx) => *idx,
            Mapping::Level2(_, idx) => *idx,
            Mapping::Level1(_, idx) => *idx,
            Mapping::Level0(_, idx) => *idx,
        };

        &&& idx < PAGE_TABLE_ENTRY
    }
}

impl Mapping {
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

/// Map and validate the specified virtual memory region at `paddr`.
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
        Ghost(i): Ghost<usize>
    requires
        old(ctx_perm).wf_with(ctx),
        header.wf_for_loading(old(ctx_perm).pgtable_perm.mapping_space),
        vaddr_start.wf(),
        vaddr_end.wf(),
        paddr.wf(),
        vaddr_start@ % PAGE_SIZE == 0,
        vaddr_end@ % PAGE_SIZE == 0,
        vaddr_start@ < vaddr_end@ < u64::MAX,
        paddr@ % PAGE_SIZE == 0,
        paddr@ + (vaddr_end@ - vaddr_start@) < 0x000f_ffff_ffff_f000,
    ensures
        ctx_perm.wf_with(ctx),
        ctx_perm.pgtable_perm.mapped_region(vaddr_start..vaddr_end),
)]
pub(crate) fn map_and_validate_elf_segment(
    ctx: DekoPPtr<DekoCpuCtx>,
    header: Stage2LaunchInfo,
    vaddr_start: VirtAddr,
    vaddr_end: VirtAddr,
    paddr: PhysAddr,
) {
    broadcast use PteFlags::lemma_each_bits_is_valid;

    log_str!("Mapping and validating ELF segment from [");
    log_hex_prefixed!(vaddr_start.0);
    log_str!("] to [");
    log_hex_prefixed!(vaddr_end.0);
    log_str!("] at physical address [");
    log_hex_prefixed!(paddr.0);
    log_str_ln!("]");

    let flags = PteFlags::writeable_kernel();

    proof {
        // Proof is boring but we have to repeat.
        //
        // Perhaps there is a way for us to wrap such
        // proofs inside some sort of macros to automate
        // this tedious process for any flags defined
        // inside `deko_bitflags_quick!`.
        assert(flags.bits() & Pte_ALL_BITS == flags.bits()) by {
            let p = 1u64 << 0;
            let w = 1u64 << 1;
            let u = 1u64 << 2;
            let a = 1u64 << 5;
            let d = 1u64 << 6;
            let h = 1u64 << 7;
            let g = 1u64 << 8;
            let nx = 1u64 << 63;
            let all = p | w | u | a | d | h | g | nx;

            let writeable_kernel_bits = p | w | a | d;
            assert(flags.bits() == writeable_kernel_bits & all);
            assert((writeable_kernel_bits & all) & all == (writeable_kernel_bits & all))
                by (bit_vector)
                requires
                    writeable_kernel_bits == (1u64 << 0) | (1u64 << 1) | (1u64 << 5) | (1u64 << 6),
                    all == (1u64 << 0) | (1u64 << 1) | (1u64 << 2) | (1u64 << 5) | (1u64 << 6) | (
                    1u64 << 7) | (1u64 << 8) | (1u64 << 63),
            ;
        }
    }

    let ctx_borrowed = ctx.borrow(Tracked(&ctx_perm.ptr_perm));
    let shared_bit = ctx_borrowed.shared_bit();
    let private_bit = ctx_borrowed.private_bit();
    let ms = ctx_borrowed.kernel_mapping();
    let pgtable = ctx_borrowed.pgtable();

    let virt_range = vaddr_start..vaddr_end;
    PageTable::map_page_multiple(
        pgtable,
        Tracked(&mut ctx_perm.pgtable_perm),
        virt_range,
        paddr,
        flags,
        &ms,
        private_bit,
        shared_bit,
    );
}

} // verus!
