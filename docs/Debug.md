# Debugging Support

Debugging within SNP guests presents unique challenges due to the confidential computing environment. This document outlines several techniques for debugging with the Deko monitor, particularly for unverified code components such as assembly routines and MSR protocols.

## GDB Support

GDB debugging is currently not available in the monitor, as we have not yet implemented the complete GDB remote serial protocol. While this feature is planned for future releases, implementing it requires significant engineering effort.

Currently, debugging relies on unverified `print` statements for guest observation. **Note:** This debugging feature should be disabled in production environments for security reasons.

The print mechanism varies by platform:
- **SEV-SNP guests**: Utilize the Guest-Host Communication Block (GHCB) protocol
- **TDX guests**: Use standard serial ports (COM0/COM1)

For developers interested in implementing GDB support independently, the [gdbstub](https://crates.io/crates/gdbstub) crate provides a Rust implementation of the GDB remote serial protocol.

## Logging Infrastructure

### GHCB-Based Logging (SEV-SNP)

The print functionality in SEV-SNP guests is implemented through GHCB, which emulates serial port behavior. However, this mechanism has important prerequisites:

1. **Page tables must be properly configured**
2. **Page properties must be correctly set** (RMP table entries)
3. **GHCB pages must be marked as shared** between hypervisor and guest

Due to these requirements and the complexity of the GHCB protocol, logging is unavailable during early boot stages before GHCB initialization completes.

### Early Boot Debugging

## Binary Search Debugging

During the initial boot phase, before GHCB or serial ports are available, debugging options are limited to primitive techniques:

### Available Primitives

- **`early_dbg`**: A minimal assembly wrapper around the `hlt` instruction that creates an observable infinite loop
- **`early_die`**: An assembly wrapper around the `ud2` instruction that triggers an undefined instruction exception

Both functions are implemented in pure assembly and marked with `#[verifier::external_body]` to bypass verification.

### Binary Search Technique

To locate failures during early boot:

1. **Insert `early_dbg` at suspected failure point**
   - If the system hangs → code reached this point
   - If the system crashes → failure occurs before this point

2. **Progressively narrow the search space**
   - Move the debug marker based on observed behavior
   - Continue bisecting until the exact failure point is identified

3. **Example usage:**
   ```rust
   fn boot_sequence() {
       init_step_1();
       early_dbg();  // Check if we reach here
       init_step_2();
       early_dbg();  // Move here if previous point was reached
       init_step_3();
   }
```