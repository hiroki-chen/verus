#![no_std]

use vstd::prelude::*;

verus! {

pub const BOOT_VERSION: u8 = 0x1;
    
#[repr(C)]
#[derive(Debug, Default)]
pub struct Header {
    /// The version of the boot protocol.
    pub version: u8,
    /// The boot flags.
    // pub cmdline: *const u8,
    /// The length of the cmdline string.
    pub cmdline_len: u64,
    /// The address of the Root System Description Pointer used in the ACPI programming interface.
    pub acpi2_rsdp_addr: u64,
    /// The physical address to the start of virtual address.
    pub mem_start: u64,
    /// The address to the memory mapping
    pub mmap: u64,
    /// The length of the mmap descriptors.
    pub mmap_len: u64,
    /// The kernel entry.
    pub kernel_entry: u64,
}

} // verus!