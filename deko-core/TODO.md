# TODO Items - deko-core Crate

This document tracks all TODO items and assumptions found in the deko-core crate that need to be addressed.

## High Priority Items

### Page Table Implementation (`src/mm/paging.rs`)
- [ ] **CRITICAL**: Fix tracked permissions in page table operations
  - Line: `Tracked::assume_new()` used in multiple places instead of proper tracking
  - Impact: Missing verification guarantees for page table safety
  - Files: `src/mm/paging.rs` (multiple locations)

- [ ] **CRITICAL**: Implement proper proof for `allocate_pte_lvl2_requires`
  - Line: `assume(perm.allocate_pte_lvl2_requires(...))` 
  - Impact: Missing verification of page table allocation correctness

- [ ] **Medium**: Add support for 2MB page mapping
  - Context: "Here we leave mapping 2M pages as unimplemented; BUT SOME PAGES ARE 2m"
  - Impact: Memory efficiency for large allocations

### ELF Loading (`src/elf.rs`)
- [ ] **CRITICAL**: Fix context permission tracking during ELF loading
  - Lines: Multiple `assume(ctx_perm.wf_with(ctx))` and `assume(ctx_perm == old(ctx_perm))`
  - Impact: Missing verification of memory safety during executable loading

- [ ] **High**: Proper physical address validation
  - Lines: `assume(paddr@ % PAGE_SIZE == 0)`, `assume(paddr.wf())`
  - Impact: Memory alignment guarantees

### Hardware Abstraction Layer (`src/hal.rs`)
- [ ] **High**: Implement proper CPUID table registration
  - Line: "TODO: Register the CPUID table: so that we know cpuids of each core"
  - Impact: Per-core CPU feature detection

- [ ] **CRITICAL**: Fix multiple memory layout assumptions
  - Lines: Multiple `assume()` calls for memory region bounds and alignment
  - Impact: Memory safety and layout correctness

## Medium Priority Items

### Policy Engine / Domains (`src/policy/*`)
- [ ] **High**: Add an explicit policy-loading SVSM protocol
  - Goal: inject policy bytes into the guest through a dedicated extend service instead of overloading existing launch/map paths
  - Suggested entry: add a new protocol alongside `DEKO_SERVICE_EXTEND_REPORT_APP`, `DEKO_SERVICE_EXTEND_LAUNCH_APP`, and `DEKO_SERVICE_EXTEND_MAP_IFC`
  - Output: `policy bytes -> PolicyConfigToml -> FiniteLattice / PolicyDomain`

- [ ] **High**: Refactor `DekoPolicyEngine` into a multi-domain registry
  - Goal: manage multiple `PolicyDomain`s instead of a single lattice
  - Suggested mappings:
    - `domain_id -> PolicyDomain`
    - `app identity -> domain_id`
  - Domain should be the main abstraction, with lattice as one component inside a domain

- [ ] **High**: Associate loaded policy with namespace / workspace metadata
  - Goal: bind policy domains to some cloud-native selector such as namespace, workspace, or similar tenant identifier
  - Keep this mapping separate from lattice semantics
  - Suggested shape: `DomainSelector -> DomainId`

- [ ] **High**: Bind apps to domains during app registration
  - Goal: determine domain ownership at `report_app` time, not lazily at first syscall
  - Suggested hook: `handle_deko_service_report_app`
  - Result: `pid/tgid/measurement/... -> DomainId`

- [ ] **High**: Require launch-time domain resolution
  - Goal: refuse app launch if the app has not been bound to a policy domain
  - Suggested hook: `handle_deko_service_launch_app`
  - This keeps launch semantics simple and makes later IFC enforcement deterministic

- [ ] **High**: Make cross-domain communication forbidden by default
  - Goal: any interaction with `src_domain != dst_domain` is denied unless an explicit cross-domain policy allows it
  - Treat this as a top-level policy-engine rule rather than scattering it across individual syscall handlers

- [ ] **Medium**: Separate trusted parsing from verified policy compilation more cleanly
  - Current state: parser is a trusted boundary; `FiniteLattice::compile` is verified
  - Next step: shrink the trusted parser boundary to TOML decoding only, and keep raw-to-internal conversion as small and auditable as possible

### Memory Management
- [ ] **Frame Allocator** (`src/mm/frame_allocator.rs`):
  - Implement proper return value with provenance tracking
  - Complete deallocation function (currently `crate::die("todo")`)

- [ ] **Memory Module** (`src/mm/mod.rs`):
  - Implement proper memory mapping functionality
  - Fix `Tracked::assume_new()` usage

### SNP (Secure Nested Paging) Support (`src/snp/mod.rs`)
- [ ] **Medium**: Remove hardcoded physical address sizes
  - Line: `phys_addr_sizes: 48` (hardcoded)
  - Impact: Platform compatibility

- [ ] **High**: Implement proper validation functions
  - Line: `if validate { true } else { true }` - placeholder logic
  - Impact: Security validation

- [ ] **Medium**: Complete RMP (Reverse Map Table) adjustment specification
  - Line: "todo: old(perm).rmpadjust_spec == perm"

### GHCB (Guest-Hypervisor Communication Block) (`src/snp/ghcb.rs`)
- [ ] **Medium**: Implement proper virtual-to-physical address conversion
  - Line: `// let ghcb_paddr = virt_to_phys(ghcb_vaddr); // todo: FIX ME.`
  - Impact: Guest-hypervisor communication reliability

## Low Priority Items

### Code Organization (`src/lib.rs`)
- [ ] **Low**: Split crate into three logical parts
  - Line: "TODO: Split our crate into three parts"
  - Impact: Code maintainability

### TDX (Trust Domain Extensions) (`src/tdx/tdcall.rs`)
- [ ] **Medium**: Add proper preconditions for leaf functions
  - Context: "TODO: for `requires` we need to add the precondition that the leaf function is always within what we have defined"
  - Impact: TDX call verification

### CPU Management (`src/cpu/mod.rs`)
- [ ] **Low**: Implement IPI (Inter-Processor Interrupt) state tracking
  - Line: `// ipi_state: IpiState, todo`
  - Impact: Multi-core coordination

### Boot Process (`src/boot/mod.rs`)
- [ ] **Low**: Implement actual Linux boot header
  - Line: "TODO: This is a placeholder for the actual linux boot header"
  - Impact: Linux compatibility

### Logging (`src/logging.rs`)
- [ ] **Medium**: Overhaul logging module for both SNP and TDX
  - Line: "TODO: Overhaul this module to fit both snp and tdx"
  - Impact: Debugging and monitoring

## Critical Assumptions Requiring Verification

### Memory Safety Assumptions
- [ ] **Physical address alignment**: Multiple assumptions about PAGE_SIZE alignment
- [ ] **Memory region bounds**: Assumptions about memory regions fitting within valid ranges
- [ ] **Address conversion correctness**: Virtual-to-physical address mapping assumptions

### Verification Gaps
- [ ] **Page table operations**: Missing proofs for page table manipulation safety
- [ ] **ELF loading**: Incomplete verification of executable loading process
- [ ] **Context management**: Assumptions about CPU context preservation

### Security Assumptions
- [ ] **SNP validation**: Placeholder validation logic needs implementation
- [ ] **TDX preconditions**: Missing verification for trusted execution
- [ ] **Permission tracking**: Multiple uses of `assume_new()` instead of proper tracking

## Recommended Action Plan

### Phase 1 (Critical)
- [ ] Fix all `Tracked::assume_new()` usages with proper permission tracking
- [ ] Implement missing proofs for page table allocation
- [ ] Complete ELF loading verification

### Phase 2 (High Priority)
- [ ] Implement proper memory layout verification
- [ ] Complete SNP validation functions
- [ ] Fix CPUID table registration

### Phase 3 (Medium Priority)
- [ ] Add 2MB page support
- [ ] Complete frame allocator implementation
- [ ] Overhaul logging system

### Phase 4 (Low Priority)
- [ ] Code organization improvements
- [ ] Linux boot header implementation
- [ ] IPI state tracking

---

**Last Updated**: November 11, 2025  
**Total Items**: 65 TODO/assumption instances found  
**Critical Issues**: 8  
**High Priority**: 6  
**Medium Priority**: 8  
**Low Priority**: 5
