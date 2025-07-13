#![no_std]

use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

pub const BOOT_VERSION: u8 = 0x1;

#[repr(C)]
#[derive(Debug, Default)]
pub tracked struct HeaderRaw {
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
    /// The type of this platform:
    pub platform_type: u64,
}

impl HeaderRaw {
    #[verifier::inline]
    pub open spec fn is_supported_platform(&self) -> bool {
        match &self.platform_type {
            0x0001 | 0x0002 => true,
            _ => false,
        }
    }
}

impl WellFormed for HeaderRaw {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        // The Header is well-formed if the version is valid and the addresses are aligned.
        &&& self.version == BOOT_VERSION
        &&& self.mem_start % 0x1000 == 0
        &&& self.mmap % 0x10 == 0
        &&& self.kernel_entry % 0x1000 == 0
        &&& self.is_supported_platform()
    }
}

impl IsConstant for HeaderRaw {
    #[verifier::inline]
    open spec fn is_constant(&self) -> bool {
        // The Header is constant if the version is constant and the addresses are constant.
        &&& self.version.is_constant()
        &&& self.cmdline_len.is_constant()
        &&& self.acpi2_rsdp_addr.is_constant()
        &&& self.mem_start.is_constant()
        &&& self.mmap.is_constant()
        &&& self.mmap_len.is_constant()
        &&& self.kernel_entry.is_constant()
    }
}

} // verus!
