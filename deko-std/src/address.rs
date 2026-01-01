//! Address management for x86-64 canonical addresses and memory mapping.
//!
//! This module provides safe abstractions for virtual and physical addresses in the Deko hypervisor,
//! ensuring all virtual addresses conform to x86-64 canonical form requirements. It includes
//! automatic canonicalization, memory mapping utilities, and formally verified address operations.
//!
//! # Key Features
//!
//! - **Canonical Address Handling**: Automatic conversion to x86-64 canonical form
//! - **Memory Safety**: Well-formedness checks and verification properties
//! - **Address Translation**: Virtual-to-physical mapping abstractions
//! - **Formal Verification**: Mathematically proven correctness properties
//!
//! # Address Ranges
//!
//! x86-64 uses 48-bit virtual addresses with two canonical ranges:
//! - Lower: `0x0000_0000_0000_0000` to `0x0000_7FFF_FFFF_FFFF` (user space)
//! - Upper: `0xFFFF_8000_0000_0000` to `0xFFFF_FFFF_FFFF_FFFF` (kernel space)
//!
//! # Example
//!
//! ```rust
//! use deko_std::address::{VirtAddr, PhysAddr};
//!
//! // Create canonical virtual addresses
//! let vaddr = VirtAddr::new(0x1234_5678_9ABC_DEF0);
//! let paddr = PhysAddr::from(0x0000_0001_0000_0000);
//!
//! // Address is automatically canonicalized
//! assert!(vaddr.wf()); // Always true
//! ```
use deko_macros::DekoDebug;
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpecImpl, PartialOrdSpecImpl};

use crate::prelude::*;

verus! {

#[verifier::inline]
pub const PHYS_MAX_ADDR: u64 = 0x0000_FFFF_FFFF_FFFFu64;

/// Maximum number of bits used in x86-64 virtual addresses.
#[verifier::inline]
pub spec const VADDR_MAX_BITS: nat = 48;

/// Mask for the lower canonical address range (user space).
///
/// This represents the maximum address in the lower canonical range:
/// `0x0000_7FFF_FFFF_FFFF` (bit 47 clear, all others can be set).
#[verifier::inline]
pub const VADDR_LOWER_MASK: u64 = 0x0000_7FFF_FFFF_FFFFu64;

/// Mask for the upper canonical address range (kernel space).
///
/// This represents the minimum address in the upper canonical range:
/// `0xFFFF_8000_0000_0000` (bits 47-63 set, others clear).
#[verifier::inline]
pub const VADDR_UPPER_MASK: u64 = 0xFFFF_8000_0000_0000u64;

/// Size of the 48-bit virtual address space (2^48 bytes).
#[verifier::inline]
pub const VADDR_RANGE_SIZE: u64 = 0x1_0000_0000_0000u64;

/// Checks if bit 47 (the sign bit) is set in an address.
///
/// This determines whether an address should be sign-extended to the upper
/// canonical range (bit 47 set) or lower canonical range (bit 47 clear).
#[verifier::inline]
pub open spec fn check_sign_bit(addr: u64) -> bool {
    addr & (1u64 << 47) == 1u64 << 47
}

/// Extracts the lower 48 bits of an address.
///
/// This preserves the actual address bits while clearing any upper bits
/// that may not be in canonical form.
#[verifier::inline]
pub open spec fn vaddr_lower_bits(addr: u64) -> u64 {
    addr & VADDR_LOWER_MASK
}

/// Extracts the upper 16 bits of an address.
///
/// This isolates the sign-extension bits (48-63) used for canonicalization.
#[verifier::inline]
pub open spec fn vaddr_upper_bits(addr: u64) -> u64 {
    addr & VADDR_UPPER_MASK
}

/// Implementation of sign extension based on bit 47.
///
/// If bit 47 is set, creates an upper canonical address by combining
/// the lower bits with the upper mask. Otherwise, returns just the lower bits.
pub open spec fn sign_extend_impl(addr: u64) -> u64 {
    if check_sign_bit(addr) {
        (vaddr_lower_bits(addr) + VADDR_UPPER_MASK) as u64
    } else {
        vaddr_lower_bits(addr)
    }
}

/// Specification for canonical address conversion.
///
/// Converts any 64-bit value to a canonical x86-64 virtual address by:
/// 1. Preserving addresses already in the lower canonical range
/// 2. Mapping intermediate values to the upper canonical range
/// 3. Using bit 47 to determine the target range for other values
pub open spec fn sign_extend_spec(addr: u64) -> u64
    recommends
        addr < VADDR_RANGE_SIZE,
{
    if addr <= VADDR_LOWER_MASK {
        addr
    } else if addr < VADDR_RANGE_SIZE {
        (addr - VADDR_LOWER_MASK - 1 + VADDR_UPPER_MASK) as u64
    } else {
        sign_extend_impl(addr)
    }
}

pub broadcast proof fn lemma_aligned_vaddr_pfn_preserves_order(lhs: VirtAddr, rhs: VirtAddr)
    requires
        lhs.wf(),
        rhs.wf(),
        lhs@ % PAGE_SIZE == 0,
        rhs@ % PAGE_SIZE == 0,
    ensures
        #![trigger lhs.pfn(), rhs.pfn()]
        lhs@ <= rhs@ ==> lhs.pfn()@ <= rhs.pfn()@,
        lhs@ > rhs@ ==> lhs.pfn()@ > rhs.pfn()@,
{
    if lhs@ <= rhs@ {
        let lhs = lhs@;
        let rhs = rhs@;

        assert(lhs >> 12 <= rhs >> 12) by (bit_vector)
            requires
                lhs % PAGE_SIZE == 0,
                rhs % PAGE_SIZE == 0,
                lhs <= rhs,
        ;
    }
    if lhs@ > rhs@ {
        let lhs = lhs@;
        let rhs = rhs@;

        assert(lhs >> 12 > rhs >> 12) by (bit_vector)
            requires
                lhs % PAGE_SIZE == 0,
                rhs % PAGE_SIZE == 0,
                lhs > rhs,
        ;
    }
}

/// Proves that sign extension always produces canonical addresses.
///
/// This lemma establishes that any result from sign extension will be in one of the
/// two canonical address ranges, ensuring memory safety and processor compatibility.
pub proof fn lemma_sign_extend_make_canonical(addr: u64, ret: u64)
    requires
        sign_extend_ensures(addr, ret),
    ensures
        ret <= VADDR_LOWER_MASK || ret >= VADDR_UPPER_MASK,
{
    if addr <= VADDR_LOWER_MASK {
        // trivial
    } else if addr < VADDR_RANGE_SIZE {
        assert(ret == (addr - VADDR_LOWER_MASK - 1 + VADDR_UPPER_MASK) as u64);

        assert(addr < VADDR_RANGE_SIZE);
        assert(addr - VADDR_LOWER_MASK >= 1);
        assert(addr - VADDR_LOWER_MASK - 1 >= 0);

        // The result is VADDR_UPPER_MASK + (addr - VADDR_LOWER_MASK - 1)
        // Since (addr - VADDR_LOWER_MASK - 1) >= 0, we have ret >= VADDR_UPPER_MASK
        assert(ret >= VADDR_UPPER_MASK);
    } else {
        // Case 3: addr >= VADDR_RANGE_SIZE
        // sign_extend_spec returns sign_extend_impl(addr)
        assert(ret == sign_extend_impl(addr));

        if check_sign_bit(addr) {
            // Bit 47 is set, so ret = vaddr_lower_bits(addr) + VADDR_UPPER_MASK
            assert(ret == (vaddr_lower_bits(addr) + VADDR_UPPER_MASK) as u64);

            // vaddr_lower_bits(addr) = addr & VADDR_LOWER_MASK
            // Since VADDR_LOWER_MASK = 0x0000_7FFF_FFFF_FFFF,
            // vaddr_lower_bits(addr) <= VADDR_LOWER_MASK
            // So ret = vaddr_lower_bits(addr) + VADDR_UPPER_MASK >= VADDR_UPPER_MASK
            assert(vaddr_lower_bits(addr) <= VADDR_LOWER_MASK) by {
                bit_u64_and_auto();
            }
        } else {
            bit_u64_and_auto();
        }
    }

    // In all cases, we've shown ret <= VADDR_LOWER_MASK || ret >= VADDR_UPPER_MASK
}

/// Postcondition specification for sign extension.
///
/// Ensures that the result matches the specification and preserves the lower 48 bits.
/// This is used to verify the correctness of the sign extension implementation.
#[verifier::inline]
pub open spec fn sign_extend_ensures(addr: u64, ret: u64) -> bool {
    &&& ret == sign_extend_spec(addr)
    &&& vaddr_lower_bits(ret) == vaddr_lower_bits(addr)
}

/// Converts any 64-bit value to a canonical x86-64 virtual address.
///
/// This is the core function that implements canonical address conversion by checking
/// bit 47 and either setting all upper bits (if set) or clearing all upper bits (if clear).
///
/// # Properties
///
/// - Always produces a canonical address
/// - Preserves the lower 48 bits of the input
/// - Maintains page alignment if present
///
/// # Example
///
/// ```rust
/// let canonical = sign_extend(0x1234_5678_9ABC_DEF0);
/// // Result will be in canonical form
/// ```
pub const fn sign_extend(addr: u64) -> (r: u64)
    ensures
        sign_extend_ensures(addr, r),
{
    let mask = 1u64 << 47;

    let v = if (addr & mask) == mask {
        addr | VADDR_UPPER_MASK
    } else {
        addr & VADDR_LOWER_MASK
    };

    proof {
        if (addr & mask) == mask {
            assert((addr | VADDR_UPPER_MASK) & VADDR_LOWER_MASK == addr & VADDR_LOWER_MASK)
                by (bit_vector);
        } else {
            assert((addr & VADDR_LOWER_MASK) & VADDR_LOWER_MASK == addr & VADDR_LOWER_MASK)
                by (bit_vector);
        }

        assert(vaddr_lower_bits(v) == vaddr_lower_bits(addr));

        // Now we prove that v == sign_extend_spec(addr)
        if addr <= VADDR_LOWER_MASK {
            assert((addr & mask) != mask) by (bit_vector)
                requires
                    addr <= VADDR_LOWER_MASK,
                    mask == 1u64 << 47,
            ;
            assert((addr & VADDR_LOWER_MASK == addr)) by (bit_vector)
                requires
                    addr <= VADDR_LOWER_MASK,
            ;
            assert(v == sign_extend_spec(addr));  // QED here
        } else if addr < VADDR_RANGE_SIZE {
            // (addr - VADDR_LOWER_MASK - 1 + VADDR_UPPER_MASK) as u64
            if (addr & mask) == mask {
                assert((addr | VADDR_UPPER_MASK) == (addr - VADDR_LOWER_MASK - 1
                    + VADDR_UPPER_MASK)) by (bit_vector)
                    requires
                        (addr & mask) == mask,
                        addr < VADDR_RANGE_SIZE,
                        mask == 1u64 << 47,
                        VADDR_LOWER_MASK == 0x0000_7FFF_FFFF_FFFFu64,
                        VADDR_UPPER_MASK == 0xFFFF_8000_0000_0000u64,
                ;
            } else {
                assert((addr & VADDR_LOWER_MASK) == (addr - VADDR_LOWER_MASK - 1
                    + VADDR_UPPER_MASK)) by (bit_vector)
                    requires
                        (addr & mask) != mask,
                        VADDR_LOWER_MASK < addr < VADDR_RANGE_SIZE,
                        mask == 1u64 << 47,
                        VADDR_LOWER_MASK == 0x0000_7FFF_FFFF_FFFFu64,
                        VADDR_UPPER_MASK == 0xFFFF_8000_0000_0000u64,
                ;
            }
        } else {
            if (addr & mask) == mask {
                // prove that v == vaddr_lower_bits(addr) + VADDR_UPPER_MASK
                assert(((addr & VADDR_LOWER_MASK) + VADDR_UPPER_MASK) == (addr | VADDR_UPPER_MASK))
                    by (bit_vector)
                    requires
                        mask == 1u64 << 47,
                        VADDR_LOWER_MASK == 0x0000_7FFF_FFFF_FFFFu64,
                        VADDR_UPPER_MASK == 0xFFFF_8000_0000_0000u64,
                ;
            } else {
                // auto.
            }
        }
    }

    v
}

/// Aligns arbitrary address `addr` upwards to the next multiple of `align`.
#[inline]
pub fn align_up(addr: u64, align: u64) -> (r: u64)
    requires
        0 < align < u64::MAX,
        is_power_of_two_spec(align as nat),
        addr + align <= u64::MAX,
    ensures
        r >= addr,
        r % align == 0,
        r < addr + align,
{
    broadcast use vstd::arithmetic::power2::lemma_pow2;
    broadcast use vstd::arithmetic::power::lemma_pow_increases;

    let mask = align - 1;
    let r = (addr + mask) & !mask;

    proof {
        crate::math::lemma_is_power_of_two_equiv(align);
        // First prove the bitwise property
        assert(r >= addr && (r & mask) == 0 && r < addr + align) by (bit_vector)
            requires
                r == ((addr + mask) as u64) & !(mask as u64),
                mask == (align - 1) as u64,
                align > 0,
                addr + align <= u64::MAX,
                (align & mask) == 0  // align is power of 2
                ,
        ;

        let n = choose|n: nat| align as nat == vstd::arithmetic::power::pow(2, n);
        assert(n < 64) by {
            if n >= 64 {
                vstd::arithmetic::power2::lemma2_to64();

                assert(align == vstd::arithmetic::power::pow(2, n));
                assert(align >= u64::MAX);
            }
        }

        assert(r % align == 0) by {
            vstd::arithmetic::power2::lemma_pow2(n);
            vstd::bits::lemma_u64_low_bits_mask_is_mod(r, n);
        };
    }

    r
}

/// A complete address mapping space containing kernel and physical memory mappings.
///
/// This structure combines separate mapping ranges for kernel memory and physical memory,
/// providing a unified interface for address translation throughout the hypervisor.
///
/// # Fields
///
/// - `kernel`: Mapping range for kernel memory regions
/// - `physmap`: Mapping range for physical memory access
///
/// # Example
///
/// ```rust
/// let mapping_space = MappingSpace {
///     kernel: kernel_mapping_range,
///     physmap: physmap_mapping_range,
/// };
/// let vaddr = mapping_space.phys_to_virt(paddr);
/// ```
#[derive(Copy, DekoDebug)]
#[repr(C)]
pub struct MappingSpace {
    pub kernel: FixedAddressMappingRange,
    pub physmap: FixedAddressMappingRange,
}

impl Clone for MappingSpace {
    fn clone(&self) -> (r: Self)
        returns
            *self,
    {
        *self
    }
}

/// Predicate for verifying MappingSpace well-formedness.
///
/// This predicate ensures that a MappingSpace instance satisfies all
/// necessary invariants for safe address translation operations.
pub struct MappingSpacePred;

impl Predicate<MappingSpace> for MappingSpacePred {
    open spec fn inv(self, v: MappingSpace) -> bool {
        v.wf()
    }
}

/// A fixed mapping between contiguous virtual and physical address ranges.
///
/// This structure represents a linear mapping where virtual addresses in the range
/// `[virt_start, virt_end)` map to physical addresses starting at `phys_start`.
/// The mapping preserves offsets, so `virt_start + offset` maps to `phys_start + offset`.
///
/// # Fields
///
/// - `virt_start`: Starting virtual address of the mapped range
/// - `virt_end`: Ending virtual address of the mapped range (exclusive)
/// - `phys_start`: Starting physical address that the virtual range maps to
///
/// # Invariants
///
/// - All addresses must be well-formed
/// - Virtual range must be non-empty (`virt_start < virt_end`)
/// - No arithmetic overflow in address calculations
///
/// # Example
///
/// ```rust
/// let mapping = FixedAddressMappingRange::new(
///     VirtAddr::new(0xFFFF_8000_0000_0000),
///     VirtAddr::new(0xFFFF_8000_1000_0000),
///     PhysAddr::from(0x0000_0000_1000_0000),
/// );
///
/// if mapping.in_range(paddr) {
///     let vaddr = mapping.phys_to_virt(paddr);
/// }
/// ```
#[derive(Clone, Copy, DekoDebug)]
#[repr(C)]
pub struct FixedAddressMappingRange {
    pub virt_start: VirtAddr,
    pub virt_end: VirtAddr,
    pub phys_start: PhysAddr,
}

impl FixedAddressMappingRange {
    /// Creates a dummy mapping range. This area is never used.
    pub fn dummy() -> (r: Self)
        returns
            (Self {
                virt_start: VirtAddr::new(0),
                virt_end: VirtAddr::new(0x1000),
                phys_start: PhysAddr(0),
            }),
    {
        Self {
            virt_start: VirtAddr::new(0),
            virt_end: VirtAddr::new(0x1000),
            phys_start: PhysAddr(0),
        }
    }
}

impl WellFormed for FixedAddressMappingRange {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& Self::valid_mapping_range(self.virt_start, self.virt_end, self.phys_start)
    }
}

impl WellFormed for MappingSpace {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.kernel.wf()
        &&& self.physmap.wf()
        // &&& self.kernel.virt_start == VirtAddr::new_spec(STAGE2_START as u64)
        // &&& self.physmap.virt_start == VirtAddr::new_spec(0 as u64)
        // &&& self.physmap.virt_end == VirtAddr::new_spec(LOWMEM_END as u64)

    }
}

impl FixedAddressMappingRange {
    /// Validates that a mapping range satisfies all safety requirements.
    ///
    /// This specification function checks that:
    /// - All addresses are well-formed
    /// - Virtual range is non-empty
    /// - No arithmetic overflow occurs in address calculations
    #[verifier::inline]
    pub open spec fn valid_mapping_range(
        virt_start: VirtAddr,
        virt_end: VirtAddr,
        phys_start: PhysAddr,
    ) -> bool {
        &&& virt_start.wf()
        &&& virt_end.wf()
        &&& phys_start.wf()
        &&& phys_start@ % PAGE_SIZE == 0 && virt_start@ % PAGE_SIZE == 0 && virt_end@ % PAGE_SIZE
            == 0
        &&& virt_start@ < virt_end@
        &&& phys_start@ + virt_end@ - virt_start@ <= 0x000f_ffff_ffff_f000
    }

    /// Creates a new fixed address mapping range.
    ///
    /// # Arguments
    ///
    /// - `virt_start`: Starting virtual address of the range
    /// - `virt_end`: Ending virtual address of the range (exclusive)
    /// - `phys_start`: Starting physical address that maps to `virt_start`
    ///
    /// # Returns
    ///
    /// A well-formed mapping range that can be used for address translation.
    ///
    /// # Example
    ///
    /// ```rust
    /// let mapping = FixedAddressMappingRange::new(
    ///     VirtAddr::new(0xFFFF_8000_0000_0000),
    ///     VirtAddr::new(0xFFFF_8000_1000_0000),
    ///     PhysAddr::from(0x0000_0000_1000_0000),
    /// );
    /// ```
    pub fn new(virt_start: VirtAddr, virt_end: VirtAddr, phys_start: PhysAddr) -> (r: Self)
        requires
            Self::valid_mapping_range(virt_start, virt_end, phys_start),
        ensures
            r.wf(),
            r.virt_start == virt_start,
            r.virt_end == virt_end,
            r.phys_start == phys_start,
    {
        Self { virt_start, virt_end, phys_start }
    }

    /// Specification for checking if a physical address is within the mapped range.
    #[verifier::inline]
    pub open spec fn in_range_spec(&self, paddr: PhysAddr) -> bool {
        &&& paddr@ >= self.phys_start@
        &&& paddr@ < self.phys_start@ + (self.virt_end@ - self.virt_start@)
    }

    /// Checks if a physical address is within this mapping range.
    ///
    /// # Arguments
    ///
    /// - `paddr`: Physical address to check
    ///
    /// # Returns
    ///
    /// `true` if the physical address can be translated by this mapping range.
    ///
    /// # Example
    ///
    /// ```rust
    /// if mapping.in_range(paddr) {
    ///     let vaddr = mapping.phys_to_virt(paddr);
    ///     // Use the translated virtual address
    /// }
    /// ```
    #[inline]
    #[verifier::when_used_as_spec(in_range_spec)]
    pub fn in_range(&self, paddr: PhysAddr) -> (r: bool)
        requires
            self.wf(),
            paddr.wf(),
        ensures
            r == self.in_range_spec(paddr),
    {
        paddr.0 >= self.phys_start.0 && paddr.0 < self.phys_start.0 + (self.virt_end.0
            - self.virt_start.0)
    }

    /// Specification for physical-to-virtual address translation.
    #[verifier::inline]
    pub open spec fn phys_to_virt_spec(&self, paddr: PhysAddr) -> VirtAddr
        recommends
            self.in_range_spec(paddr),
    {
        let offset = paddr@ - self.phys_start@;

        VirtAddr::new((self.virt_start@ + offset) as u64)
    }

    /// Translates a physical address to its corresponding virtual address.
    ///
    /// This function performs a linear translation by calculating the offset from
    /// the physical base and adding it to the virtual base address.
    ///
    /// # Arguments
    ///
    /// - `paddr`: Physical address to translate (must be within range)
    ///
    /// # Returns
    ///
    /// The corresponding canonical virtual address.
    ///
    /// # Example
    ///
    /// ```rust
    /// let paddr = PhysAddr::from(0x0000_0000_1234_5000);
    /// if mapping.in_range(paddr) {
    ///     let vaddr = mapping.phys_to_virt(paddr);
    ///     assert!(vaddr.wf()); // Always canonical
    /// }
    /// ```
    #[verifier::when_used_as_spec(phys_to_virt_spec)]
    pub fn phys_to_virt(&self, paddr: PhysAddr) -> (vaddr: VirtAddr)
        requires
            self.wf(),
            paddr.wf(),
            self.in_range_spec(paddr),
        ensures
            vaddr.wf(),
            vaddr == self.phys_to_virt_spec(paddr),
    {
        let vaddr = self.virt_start.0 + (paddr.0 - self.phys_start.0);

        // Add the offset to the virt base.
        VirtAddr::new(vaddr)
    }
}

impl MappingSpace {
    pub open spec fn phys_to_virt_spec(&self, paddr: PhysAddr) -> VirtAddr
        recommends
            self.kernel.in_range_spec(paddr) || self.physmap.in_range_spec(paddr),
    {
        if self.kernel.in_range_spec(paddr) {
            self.kernel.phys_to_virt_spec(paddr)
        } else {
            self.physmap.phys_to_virt_spec(paddr)
        }
    }

    /// Translates a physical address using the appropriate mapping range.
    ///
    /// This function automatically selects between kernel and physmap ranges
    /// based on which range contains the given physical address.
    ///
    /// # Arguments
    ///
    /// - `paddr`: Physical address to translate
    ///
    /// # Returns
    ///
    /// The corresponding canonical virtual address.
    ///
    /// # Panics
    ///
    /// Panics if the physical address is not within either mapping range.
    ///
    /// # Example
    ///
    /// ```rust
    /// let mapping_space = MappingSpace { kernel, physmap };
    /// let vaddr = mapping_space.phys_to_virt(paddr);
    /// ```
    pub fn phys_to_virt(&self, paddr: PhysAddr) -> (vaddr: Option<VirtAddr>)
        requires
            self.wf(),
            paddr.wf(),
            self.kernel.in_range_spec(paddr) || self.physmap.in_range_spec(paddr),
        ensures
            vaddr.wf(),
            vaddr matches Some(vaddr) && vaddr == self.phys_to_virt_spec(paddr),
    {
        if self.kernel.in_range(paddr) {
            return Some(self.kernel.phys_to_virt(paddr));
        } else if self.physmap.in_range(paddr) {
            return Some(self.physmap.phys_to_virt(paddr));
        }
        // Never happens here

        proof {
            assert(false);
        }
        None
    }
}

/// A canonical virtual address wrapper that ensures x86-64 address requirements.
///
/// This type automatically converts any input address to canonical form, ensuring
/// that all virtual addresses conform to x86-64 processor requirements. Virtual
/// addresses must have bits 48-63 as sign extensions of bit 47.
///
/// # Properties
///
/// - Always maintains canonical form
/// - Preserves lower 48 bits of input addresses
/// - Implements well-formedness checking
/// - Supports conversion from various numeric types and pointers
///
/// # Example
///
/// ```rust
/// let vaddr = VirtAddr::new(0x1234_5678_9ABC_DEF0);
/// assert!(vaddr.wf()); // Always true - automatically canonicalized
///
/// // Works with different input types
/// let from_u32 = VirtAddr::from(0x12345678u32);
/// let from_ptr = VirtAddr::from(ptr as *const u8);
/// ```
#[derive(Eq, Clone, Default, Copy, DekoDebug)]
#[repr(transparent)]
pub struct VirtAddr(
    #[deko(hex)]
    pub u64,
);

impl View for VirtAddr {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl VirtAddr {
    /// Proves that canonicalization preserves 4K page alignment.
    ///
    /// This lemma establishes that if an input address is aligned to a 4K page boundary,
    /// the canonicalized result will also be aligned to the same boundary. This is
    /// important for page table operations and memory management.
    pub proof fn lemma_make_canonical_preserves_alignment_4k(addr: u64, r: u64)
        requires
            addr % 0x1000 == 0,
            sign_extend_ensures(addr, r),
        ensures
            r % 0x1000 == 0,
    {
        assert(vaddr_lower_bits(addr) == vaddr_lower_bits(r));
        assert((addr & 0x0000_7FFF_FFFF_FFFFu64) % 0x1000 == 0) by (bit_vector)
            requires
                addr % 0x1000 == 0,
        ;
        assert(r % 0x1000 == 0) by (bit_vector)
            requires
                r & 0x0000_7FFF_FFFF_FFFFu64 == addr & 0x0000_7FFF_FFFF_FFFFu64,
                (addr & 0x0000_7FFF_FFFF_FFFFu64) % 0x1000 == 0,
        ;
    }

    pub broadcast proof fn lemma_page_shift_le_max(&self)
        requires
            self@ <= u64::MAX,
        ensures
            #[trigger] self@ >> 12 <= u64::MAX >> 12,
    {
        let v = self@;

        assert(v >> 12 <= u64::MAX >> 12) by (bit_vector)
            requires
                v <= u64::MAX,
        ;
    }

    pub broadcast proof fn lemma_page_size_eq_shifts(&self)
        requires
            self@ <= u64::MAX >> 12,
        ensures
            #[trigger] self@ * PAGE_SIZE == self@ << 12,
    {
        let v = self@;

        assert(v * PAGE_SIZE == v << 12) by (bit_vector)
            requires
                v <= u64::MAX >> 12,
        ;
    }

    pub broadcast proof fn lemma_pfn_roundtrip(&self)
        requires
            self.wf(),
            self@ % PAGE_SIZE == 0,
        ensures
            #[trigger] self.pfn()@ << 12 == self@,
    {
        let v = self@;

        assert(v >> 12 << 12 == v) by (bit_vector)
            requires
                v % PAGE_SIZE == 0,
        ;
    }

    /// Specification for canonical address creation.
    ///
    /// This specification function defines how a 64-bit value should be converted
    /// to a canonical virtual address using the sign extension specification.
    pub open spec fn make_canonical_spec(addr: u64) -> VirtAddr {
        let ret = sign_extend_spec(addr);

        VirtAddr(ret)
    }

    pub open spec fn page_align_up_requires(self) -> bool {
        &&& self.wf()
        &&& if self@ <= VADDR_LOWER_MASK {
            self@ + (PAGE_SIZE - 1) <= VADDR_LOWER_MASK
        } else if self@ >= VADDR_UPPER_MASK {
            self@ + (PAGE_SIZE - 1) <= u64::MAX
        } else {
            true
        }
    }

    pub open spec fn page_align_up_spec(self) -> VirtAddr {
        let r = self@ % PAGE_SIZE;

        if r == 0 {
            self
        } else {
            VirtAddr((self@ + (PAGE_SIZE - r)) as u64)
        }
    }

    pub open spec fn pfn_spec(&self) -> VirtAddr {
        VirtAddr(self@ >> 12)
    }

    /// Creates a canonical virtual address from any 64-bit value.
    ///
    /// This function converts any 64-bit input to a canonical x86-64 virtual address.
    /// In x86-64, virtual addresses must be in canonical form:
    /// - bits 0-47 are the address
    /// - bits 48-63 must be copies of bit 47 (i.e., sign-extended)
    ///
    /// This creates two valid ranges:
    /// - `0x0000_0000_0000_0000` to `0x0000_7FFF_FFFF_FFFF` (user space)
    /// - `0xFFFF_8000_0000_0000` to `0xFFFF_FFFF_FFFF_FFFF` (kernel space)
    ///
    /// # Arguments
    ///
    /// - `addr`: The 64-bit value to canonicalize
    ///
    /// # Returns
    ///
    /// A well-formed canonical virtual address
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let vaddr = VirtAddr::make_canonical(0x1234_5678_9ABC_DEF0);
    /// assert!(vaddr.wf()); // Always true
    /// ```
    #[verifier::when_used_as_spec(make_canonical_spec)]
    #[inline]
    pub const fn make_canonical(addr: u64) -> (r: Self)
        ensures
            r.wf(),
            r == Self::make_canonical_spec(addr),
            sign_extend_ensures(addr, r@),
    {
        let ret = sign_extend(addr);

        proof {
            lemma_sign_extend_make_canonical(addr, ret);
        }

        Self(ret)
    }

    #[inline]
    #[verifier::when_used_as_spec(pfn_spec)]
    pub const fn pfn(&self) -> (r: Self)
        requires
            self.wf(),
        ensures
            r == self.pfn_spec(),
    {
        VirtAddr(self.0 >> 12)
    }

    /// Specification for the primary constructor.
    ///
    /// This specification function defines the behavior of the `new` constructor
    /// in terms of the canonical address creation specification.
    pub open spec fn new_spec(addr: u64) -> VirtAddr {
        Self::make_canonical_spec(addr)
    }

    /// Creates a new canonical virtual address.
    ///
    /// This is the primary constructor for virtual addresses. It automatically
    /// canonicalizes the input value to ensure x86-64 processor compatibility.
    ///
    /// # Arguments
    ///
    /// - `addr`: The 64-bit address value to canonicalize
    ///
    /// # Returns
    ///
    /// A well-formed canonical virtual address
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let vaddr = VirtAddr::new(0x1234_5678_9ABC_DEF0);
    /// assert!(vaddr.wf()); // Always true - automatically canonicalized
    ///
    /// // Works with any 64-bit value
    /// let kernel_addr = VirtAddr::new(0xFFFF_8000_0000_1000);
    /// let user_addr = VirtAddr::new(0x0000_0000_0040_0000);
    /// ```
    #[inline]
    #[verifier::when_used_as_spec(new_spec)]
    pub const fn new(addr: u64) -> (r: Self)
        ensures
            r.wf(),
            r == Self::new_spec(addr),
            sign_extend_ensures(addr, r@),
    {
        Self::make_canonical(addr)
    }

    /// Aligns the virtual address up to the nearest page boundary.
    #[verifier::when_used_as_spec(page_align_up_spec)]
    pub fn page_align_up(self) -> (r: Self)
        requires
            self.page_align_up_requires(),
        ensures
            r.wf(),
            r == self.page_align_up_spec(),
    {
        let v = if self.0 % PAGE_SIZE == 0 {
            self.0
        } else {
            self.0 + (PAGE_SIZE - (self.0 % PAGE_SIZE))
        };

        VirtAddr(v)
    }

    /// Checks if the virtual address is aligned to the given size.
    #[inline]
    pub const fn is_aligned_to(&self, size: u64) -> bool
        requires
            size > 0,
            is_power_of_two(size),
        returns
            self@ % (size as u64) == 0,
    {
        self.0 % (size as u64) == 0
    }
}

impl WellFormed for VirtAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        // Address must be canonical (48-bit with sign extension)
        self@ <= VADDR_LOWER_MASK || self@ >= VADDR_UPPER_MASK
    }
}

/// A physical address wrapper for hardware memory addresses.
///
/// This type represents actual hardware memory addresses without canonicality
/// requirements. Unlike virtual addresses, physical addresses can use all 64 bits
/// and don't need sign extension.
///
/// # Properties
///
/// - No canonicality requirements
/// - Always well-formed (all 64 bits usable)
/// - Used for actual hardware memory access
/// - Supports conversion from various numeric types and pointers
///
/// # Example
///
/// ```rust
/// let paddr = PhysAddr::from(0x0000_0001_0000_0000);
/// assert!(paddr.wf()); // Always true
///
/// // Direct construction
/// let paddr2 = PhysAddr(0x1234_5678_9ABC_DEF0);
/// ```
#[derive(Eq, Clone, Copy, Debug, Default, DekoDebug)]
#[repr(transparent)]
pub struct PhysAddr(
    #[deko(hex)]
    pub u64,
);

impl View for PhysAddr {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl WellFormed for PhysAddr {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl vstd::std_specs::convert::FromSpecImpl<u64> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: u64) -> VirtAddr {
        VirtAddr::new_spec(value)
    }
}

impl From<u64> for VirtAddr {
    /// Creates a canonical virtual address from a 64-bit value.
    ///
    /// The input value is automatically canonicalized to ensure x86-64 compatibility.
    #[inline]
    fn from(value: u64) -> (r: Self) {
        VirtAddr::new(value)
    }
}

impl vstd::std_specs::convert::FromSpecImpl<u32> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: u32) -> VirtAddr {
        VirtAddr::new_spec(value as u64)
    }
}

impl From<u32> for VirtAddr {
    /// Creates a canonical virtual address from a 32-bit value.
    ///
    /// The 32-bit value is zero-extended to 64 bits, then canonicalized.
    #[inline]
    fn from(value: u32) -> (r: Self) {
        VirtAddr::new(value as u64)
    }
}

impl vstd::std_specs::convert::FromSpecImpl<u64> for PhysAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: u64) -> PhysAddr {
        PhysAddr(value)
    }
}

impl From<u64> for PhysAddr {
    /// Creates a physical address from a 64-bit value.
    ///
    /// Physical addresses don't require canonicalization and use the full 64-bit range.
    fn from(value: u64) -> (r: Self) {
        PhysAddr(value)
    }
}

impl vstd::std_specs::convert::FromSpecImpl<u32> for PhysAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: u32) -> PhysAddr {
        PhysAddr(value as u64)
    }
}

impl From<u32> for PhysAddr {
    /// Creates a physical address from a 32-bit value.
    ///
    /// The 32-bit value is zero-extended to 64 bits.
    fn from(value: u32) -> (r: Self)
        ensures
            r@ === value as u64,
    {
        PhysAddr(value as u64)
    }
}

impl<T> vstd::std_specs::convert::FromSpecImpl<*const T> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: *const T) -> VirtAddr {
        VirtAddr::new_spec(value as u64)
    }
}

impl<T> From<*const T> for VirtAddr {
    /// Creates a canonical virtual address from a const pointer.
    ///
    /// The pointer is cast to u64 and then canonicalized for x86-64 compatibility.
    fn from(value: *const T) -> Self {
        VirtAddr::new(value as u64)
    }
}

impl<T> vstd::std_specs::convert::FromSpecImpl<*const T> for PhysAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: *const T) -> PhysAddr {
        PhysAddr(value as u64)
    }
}

impl<T> From<*const T> for PhysAddr {
    /// Creates a physical address from a const pointer.
    ///
    /// The pointer is cast directly to u64 without canonicalization.
    fn from(value: *const T) -> Self {
        PhysAddr(value as u64)
    }
}

impl<T> vstd::std_specs::convert::FromSpecImpl<*mut T> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: *mut T) -> VirtAddr {
        VirtAddr::new_spec(value as u64)
    }
}

impl<T> From<*mut T> for VirtAddr {
    /// Creates a canonical virtual address from a mutable pointer.
    ///
    /// The pointer is cast to u64 and then canonicalized for x86-64 compatibility.
    fn from(value: *mut T) -> (r: Self)
        ensures
            r.wf(),
            r == Self::new_spec(value as u64),
            sign_extend_ensures(value as u64, r@),
    {
        VirtAddr::new(value as u64)
    }
}

impl<T> vstd::std_specs::convert::FromSpecImpl<*mut T> for PhysAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: *mut T) -> PhysAddr {
        PhysAddr(value as u64)
    }
}

impl<T> From<*mut T> for PhysAddr {
    /// Creates a physical address from a mutable pointer.
    ///
    /// The pointer is cast directly to u64 without canonicalization.
    fn from(value: *mut T) -> (r: Self)
        ensures
            r@ === value as u64,
    {
        PhysAddr(value as u64)
    }
}

/// A range of canonical virtual addresses.
///
/// Note when using this range, since now Verus does not support
/// [`core::iter::Iterator`] very well, you may need to manually
/// define functions to iterate over the range if needed; and to
/// avoid accidental misuse, you have to ensure that your step
/// must be mutliple of [`PAGE_SIZE`].
pub type VaddrRange = core::ops::Range<VirtAddr>;

/// A range of physical addresses.
pub type PaddrRange = core::ops::Range<PhysAddr>;

impl WellFormed for VaddrRange {
    /// The well-formedness predicate for virtual address ranges is
    /// simple as we just need to ensure the whole thing is bounded
    /// by well-formed virtual addresses.
    ///
    /// Note that we do not require that they must be aligned to
    /// [`PAGE_SIZE`] as this is just a collection of vaddr range.
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.end@ <= VADDR_LOWER_MASK || self.start@ >= VADDR_UPPER_MASK
        &&& self.start@ < self.end@ <= u64::MAX
    }
}

impl WellFormed for PaddrRange {
    /// The well-formedness predicate for physical address ranges
    /// is trivial as all physical addresses are well-formed.
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.start@ < self.end@ < 0x000f_ffff_ffff_f000u64
    }
}

#[inline]
pub fn create_vaddr_range(start: VirtAddr, len: usize) -> (r: VaddrRange)
    requires
        start@ % PAGE_SIZE == 0,
        len * PAGE_SIZE <= u64::MAX - start@,
    ensures
        r.start == start,
        r.end@ == start@ + (len as u64) * PAGE_SIZE,
        r.end@ % PAGE_SIZE == 0,
{
    proof {
        assert((start@ + len * PAGE_SIZE) % PAGE_SIZE as int == 0) by {
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                len as int,
                start@ as int,
                PAGE_SIZE as int,
            );
        }
    }

    VaddrRange { start, end: VirtAddr(start.0 + (len as u64) * PAGE_SIZE) }
}

#[inline]
pub fn create_paddr_range(start: PhysAddr, len: usize) -> (r: PaddrRange)
    requires
        len * PAGE_SIZE <= u64::MAX - start@,
    ensures
        r.start == start,
        r.end@ == start@ + (len as u64) * PAGE_SIZE,
        start@ % PAGE_SIZE == 0 ==> r.end@ % PAGE_SIZE == 0,
{
    proof {
        if start@ % PAGE_SIZE == 0 {
            assert((start@ + len * PAGE_SIZE) % PAGE_SIZE as int == 0) by {
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                    len as int,
                    start@ as int,
                    PAGE_SIZE as int,
                );
            }
        }
    }

    PaddrRange { start, end: PhysAddr(start.0 + (len as u64) * PAGE_SIZE) }
}

impl PartialOrd for VirtAddr {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl PartialEq for VirtAddr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialOrdSpecImpl for VirtAddr {
    closed spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> core::option::Option<
        core::cmp::Ordering,
    > {
        if self@ < other@ {
            core::option::Option::Some(core::cmp::Ordering::Less)
        } else if self@ > other@ {
            core::option::Option::Some(core::cmp::Ordering::Greater)
        } else {
            core::option::Option::Some(core::cmp::Ordering::Equal)
        }
    }
}

impl PartialEqSpecImpl for VirtAddr {
    closed spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self@ == other@
    }
}

impl PartialOrd for PhysAddr {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl PartialEq for PhysAddr {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialOrdSpecImpl for PhysAddr {
    closed spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> core::option::Option<
        core::cmp::Ordering,
    > {
        if self@ < other@ {
            core::option::Option::Some(core::cmp::Ordering::Less)
        } else if self@ > other@ {
            core::option::Option::Some(core::cmp::Ordering::Greater)
        } else {
            core::option::Option::Some(core::cmp::Ordering::Equal)
        }
    }
}

impl PartialEqSpecImpl for PhysAddr {
    closed spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self@ == other@
    }
}

} // verus!
