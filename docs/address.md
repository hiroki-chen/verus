# Address Management Module Documentation

## Overview

The `address.rs` module provides fundamental address management functionality for the Deko hypervisor, implementing x86-64 canonical address handling, virtual-to-physical address translation, and memory mapping abstractions. This module is critical for ensuring memory safety and correctness in the hypervisor's memory management subsystem.

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Core Constants](#core-constants)
3. [Address Types](#address-types)
4. [Canonical Address Handling](#canonical-address-handling)
5. [Memory Mapping](#memory-mapping)
6. [API Reference](#api-reference)
7. [Usage Examples](#usage-examples)
8. [Safety Considerations](#safety-considerations)
9. [Verification Properties](#verification-properties)

## Architecture Overview

### x86-64 Virtual Address Space

The x86-64 architecture uses 48-bit virtual addresses that must be in "canonical form":
- Bits 0-47: The actual address bits
- Bits 48-63: Must be copies of bit 47 (sign extension)

This creates two valid address ranges:
- **Lower canonical range**: `0x0000_0000_0000_0000` to `0x0000_7FFF_FFFF_FFFF` (user space)
- **Upper canonical range**: `0xFFFF_8000_0000_0000` to `0xFFFF_FFFF_FFFF_FFFF` (kernel space)

### Memory Layout

```
┌─────────────────────────────────────────────────────────────┐
│                    Upper Canonical Range                    │
│               0xFFFF_8000_0000_0000 - 0xFFFF_FFFF_FFFF_FFFF │
│                      (Kernel Space)                         │
├─────────────────────────────────────────────────────────────┤
│                    Non-Canonical Gap                        │
│               0x0000_8000_0000_0000 - 0xFFFF_7FFF_FFFF_FFFF │
│                      (Invalid)                              │
├─────────────────────────────────────────────────────────────┤
│                    Lower Canonical Range                    │
│               0x0000_0000_0000_0000 - 0x0000_7FFF_FFFF_FFFF │
│                      (User Space)                           │
└─────────────────────────────────────────────────────────────┘
```

## Core Constants

### Address Masks and Limits

```rust
/// Maximum number of bits used in virtual addresses (48 bits)
pub spec const VADDR_MAX_BITS: nat = 48;

/// Mask for the lower canonical address range
/// 0x0000_7FFF_FFFF_FFFF - Maximum user space address
pub const VADDR_LOWER_MASK: u64 = 0x0000_7FFF_FFFF_FFFFu64;

/// Mask for the upper canonical address range  
/// 0xFFFF_8000_0000_0000 - Minimum kernel space address
pub const VADDR_UPPER_MASK: u64 = 0xFFFF_8000_0000_0000u64;

/// Size of the 48-bit address space
/// 0x1_0000_0000_0000 - 2^48 bytes
pub const VADDR_RANGE_SIZE: u64 = 0x1_0000_0000_0000u64;

/// Base address for page table self-mapping
pub const PTE_BASE: VirtAddr = VirtAddr(0xFFFFF68000000000);
```

### Mathematical Properties

- `VADDR_LOWER_MASK + 1 = 0x0000_8000_0000_0000` (bit 47 set, others clear)
- `VADDR_UPPER_MASK = 0xFFFF_8000_0000_0000` (bits 47-63 set)
- `VADDR_LOWER_MASK & VADDR_UPPER_MASK = 0` (no overlap)
- `VADDR_LOWER_MASK | VADDR_UPPER_MASK = 0xFFFF_FFFF_FFFF_FFFF` (covers all bits except the gap)

## Address Types

### VirtAddr - Virtual Address

A wrapper around `u64` that ensures all virtual addresses are in canonical form.

```rust
#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct VirtAddr(pub u64);
```

**Key Properties:**
- Always maintains canonical form through sign extension
- Automatically converts non-canonical addresses to canonical form
- Preserves the lower 48 bits of the original address
- Implements `WellFormed` trait to verify canonicality

**Well-formedness condition:**
```rust
impl WellFormed for VirtAddr {
    open spec fn wf(&self) -> bool {
        self@ <= VADDR_LOWER_MASK || self@ >= VADDR_UPPER_MASK
    }
}
```

### PhysAddr - Physical Address

A simple wrapper around `u64` for physical addresses with no canonicality requirements.

```rust
#[derive(PartialEq, Eq, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct PhysAddr(pub u64);
```

**Key Properties:**
- No canonicality requirements (all 64 bits usable)
- Always well-formed
- Used for actual hardware memory addresses

## Canonical Address Handling

### Sign Extension Algorithm

The core of canonical address handling is the `sign_extend` function, which converts any 64-bit value into a canonical virtual address:

```rust
pub const fn sign_extend(addr: u64) -> u64
```

**Algorithm:**
1. Check bit 47 of the input address
2. If bit 47 is set: Set all upper bits (48-63) to 1 using `addr | VADDR_UPPER_MASK`
3. If bit 47 is clear: Clear all upper bits (48-63) using `addr & VADDR_LOWER_MASK`

**Mathematical Specification:**
```rust
pub closed spec fn sign_extend_spec(addr: u64) -> u64 {
    if addr <= VADDR_LOWER_MASK {
        addr  // Already canonical in lower range
    } else if addr < VADDR_RANGE_SIZE {
        (addr - VADDR_LOWER_MASK - 1 + VADDR_UPPER_MASK) as u64  // Map to upper range
    } else {
        sign_extend_impl(addr)  // Use bit 47 to determine range
    }
}
```

### Verification Properties

The sign extension function maintains several critical properties:

1. **Canonicality**: Result is always canonical
   ```rust
   ensures ret <= VADDR_LOWER_MASK || ret >= VADDR_UPPER_MASK
   ```

2. **Bit Preservation**: Lower 48 bits are preserved
   ```rust
   ensures vaddr_lower_bits(ret) == vaddr_lower_bits(addr)
   ```

3. **Alignment Preservation**: Page alignment is maintained
   ```rust
   requires addr % 0x1000 == 0
   ensures ret % 0x1000 == 0
   ```

## Memory Mapping

### FixedAddressMappingRange

Represents a contiguous mapping between virtual and physical address ranges:

```rust
pub struct FixedAddressMappingRange {
    pub virt_start: VirtAddr,    // Start of virtual range
    pub virt_end: VirtAddr,      // End of virtual range  
    pub phys_start: PhysAddr,    // Start of physical range
}
```

**Invariants:**
- Virtual range must be valid: `virt_start < virt_end`
- No overflow in virtual range: `virt_end - virt_start <= u64::MAX`
- No overflow in physical range: `phys_start + (virt_end - virt_start) <= u64::MAX`
- All addresses must be well-formed

**Operations:**
- `in_range(paddr)`: Check if physical address is within the mapped range
- `phys_to_virt(paddr)`: Convert physical address to virtual address

### MappingSpace

Combines kernel and physmap regions for complete address translation:

```rust
pub struct MappingSpace {
    pub kernel: FixedAddressMappingRange,   // Kernel memory mapping
    pub physmap: FixedAddressMappingRange,  // Physical memory mapping
}
```

**Usage:**
- Provides unified interface for physical-to-virtual translation
- Automatically selects appropriate mapping range
- Ensures all translations result in well-formed virtual addresses

## API Reference

### Core Functions

#### `VirtAddr::new(addr: u64) -> VirtAddr`
Creates a canonical virtual address from any 64-bit value.
- **Input**: Any 64-bit address
- **Output**: Canonical virtual address
- **Guarantees**: Result is always well-formed and canonical

#### `sign_extend(addr: u64) -> u64`
Low-level canonical address conversion.
- **Input**: Any 64-bit value
- **Output**: Canonical 64-bit address
- **Properties**: Preserves lower 48 bits, ensures canonicality

#### `FixedAddressMappingRange::phys_to_virt(paddr: PhysAddr) -> VirtAddr`
Converts physical address to virtual address within a mapping range.
- **Precondition**: `paddr` must be within the mapping range
- **Output**: Corresponding canonical virtual address

### Utility Functions

#### `check_sign_bit(addr: u64) -> bool`
Checks if bit 47 is set in an address.

#### `vaddr_lower_bits(addr: u64) -> u64`
Extracts the lower 48 bits of an address.

#### `vaddr_upper_bits(addr: u64) -> u64`
Extracts the upper 16 bits of an address.

## Usage Examples

### Creating Virtual Addresses

```rust
// Create canonical virtual addresses
let user_addr = VirtAddr::new(0x0000_1234_5678_9ABC);  // Lower canonical range
let kernel_addr = VirtAddr::new(0xFFFF_8765_4321_0DEF); // Upper canonical range

// Non-canonical addresses are automatically converted
let converted = VirtAddr::new(0x1234_8000_0000_0000);  // Becomes 0xFFFF_8000_0000_0000

// From various types
let from_u32 = VirtAddr::from(0x12345678u32);
let from_ptr = VirtAddr::from(ptr as *const u8);
```

### Memory Mapping

```rust
// Create a mapping range
let mapping = FixedAddressMappingRange::new(
    VirtAddr::new(0xFFFF_8000_0000_0000),  // Virtual start
    VirtAddr::new(0xFFFF_8000_1000_0000),  // Virtual end
    PhysAddr::from(0x0000_0000_1000_0000), // Physical start
)?;

// Check if physical address is in range
let paddr = PhysAddr::from(0x0000_0000_1234_5000);
if mapping.in_range(paddr) {
    let vaddr = mapping.phys_to_virt(paddr);
    println!("Physical {:x} maps to virtual {:x}", paddr.0, vaddr.0);
}

// Create complete mapping space
let mapping_space = MappingSpace {
    kernel: kernel_mapping,
    physmap: physmap_mapping,
};

// Unified translation
let vaddr = mapping_space.phys_to_virt(paddr)?;
```

### Working with Address Ranges

```rust
// Check canonicality
fn is_canonical(addr: u64) -> bool {
    addr <= VADDR_LOWER_MASK || addr >= VADDR_UPPER_MASK
}

// Determine address space
fn address_space(vaddr: VirtAddr) -> &'static str {
    if vaddr.0 <= VADDR_LOWER_MASK {
        "User space"
    } else {
        "Kernel space"
    }
}

// Extract address components
let addr = 0xFFFF_8123_4567_89AB;
let lower_bits = vaddr_lower_bits(addr);  // 0x0000_0123_4567_89AB
let upper_bits = vaddr_upper_bits(addr);  // 0xFFFF_8000_0000_0000
let sign_bit = check_sign_bit(addr);      // true
```

## Safety Considerations

### Memory Safety

1. **Canonical Address Requirement**: All virtual addresses must be canonical to avoid processor exceptions
2. **Range Validation**: Physical addresses must be validated before translation
3. **Overflow Protection**: All arithmetic operations are checked for overflow
4. **Well-formedness**: All address types implement well-formedness checks

### Common Pitfalls

1. **Non-canonical Addresses**: Never use raw 64-bit values as virtual addresses without canonicalization
2. **Range Assumptions**: Always verify physical addresses are within mapping ranges before translation
3. **Bit Manipulation**: Be careful when manually manipulating address bits - use provided functions
4. **Alignment**: Ensure proper alignment for page-based operations

### Best Practices

1. **Always use `VirtAddr::new()`** for creating virtual addresses
2. **Validate ranges** before performing address translations
3. **Use well-formedness checks** in preconditions and postconditions
4. **Leverage verification properties** in proofs and specifications

## Verification Properties

### Formal Guarantees

The module provides several formally verified properties:

1. **Canonical Preservation**: `sign_extend` always produces canonical addresses
2. **Bit Preservation**: Lower 48 bits are always preserved during canonicalization
3. **Alignment Preservation**: Page alignment is maintained through canonicalization
4. **Translation Correctness**: Address translations maintain mathematical relationships
5. **Well-formedness**: All operations preserve well-formedness invariants

### Proof Techniques

The module uses several verification techniques:

- **Bit-vector reasoning**: For low-level bit manipulation proofs
- **Arithmetic reasoning**: For address range and overflow proofs  
- **Invariant preservation**: For maintaining well-formedness
- **Case analysis**: For handling different address ranges

### Key Lemmas

- `lemma_sign_extend_make_canonical`: Proves canonicality of sign extension
- `lemma_make_canonical_preserves_alignment_4k`: Proves alignment preservation
- Various bit manipulation lemmas for correctness of address operations

## Implementation Notes

### Performance Considerations

- All address operations are designed to be efficient with minimal branching
- Bit manipulation uses hardware-optimized operations
- Canonical form checking is a simple range comparison
- Address translation is constant-time arithmetic

### Hardware Integration

- Designed specifically for x86-64 architecture requirements
- Compatible with hardware page table structures
- Supports both 4KB and large page mappings
- Integrates with processor's canonical address checking

### Future Extensions

The module is designed to support future enhancements:
- 5-level paging (57-bit addresses) when needed
- Additional mapping types and policies
- Enhanced verification properties
- Performance optimizations for specific use cases

---

This documentation provides a comprehensive overview of the address management module. For implementation details, refer to the source code in `deko-std/src/address.rs`.
