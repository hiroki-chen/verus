#![no_std]

use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

pub const BOOT_VERSION: u8 = 0x1;

// The first 640 KB of RAM (low memory)
pub const LOWMEM_END: u32 = 0xA0000;

pub const STAGE2_HEAP_START: u32 = 0x10000;

// 64 KB
pub const STAGE2_HEAP_END: u32 = LOWMEM_END;

// 640 KB
pub const STAGE2_BASE: u32 = 0x800000;

// Start of stage2 area excluding heap
pub const STAGE2_STACK_END: u32 = STAGE2_BASE;

pub const STAGE2_STACK_PAGE: u32 = 0x805000;

pub const STAGE2_INFO_SZ: u32 = 0x30;

// hardcode this.
pub const STAGE2_STACK: u32 = STAGE2_STACK_PAGE + 0x1000 - STAGE2_INFO_SZ;

pub const SECRETS_PAGE: u32 = 0x806000;

pub const CPUID_PAGE: u32 = 0x807000;

// Stage2 is loaded at 8 MB + 32 KB
pub const STAGE2_START: u32 = 0x808000;

pub const STAGE2_MAXLEN: u32 = 0x8D0000 - STAGE2_START;

/// This piece of information is provided by IGVM to stage2 so we do not
/// explicitly construct it.
///
/// The parameter's structure is defined in svsm/igvmbuilder; we can also
/// construct one on our own if needed but not necessary for the time being.
#[repr(C, packed)]
pub struct Stage2LaunchInfo {
    // VTOM must be the first field.
    pub vtom: u64,
    // platform_type must be the second field.
    pub platform_type: u32,
    // cpuid_page must be the third field.
    pub cpuid_page: u32,
    // secrets_page must be the fourth field.
    pub secrets_page: u32,
    pub stage2_end: u32,
    pub kernel_elf_start: u32,
    pub kernel_elf_end: u32,
    pub kernel_fs_start: u32,
    pub kernel_fs_end: u32,
    pub igvm_params: u32,
    pub _reserved: u32,
}

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

impl WellFormed for Stage2LaunchInfo {
    open spec fn wf(&self) -> bool {
        // The Stage2LaunchInfo is well-formed if the addresses are aligned.
        &&& self.vtom % 0x1000 == 0
        &&& self.cpuid_page % 0x1000 == 0
        &&& self.cpuid_page != 0
        &&& self.secrets_page % 0x1000 == 0
        &&& self.secrets_page != 0
        &&& self.stage2_end % 0x1000 == 0
        &&& self.kernel_elf_start % 0x1000 == 0
        &&& self.kernel_elf_end % 0x1000 == 0
        &&& self.kernel_fs_start % 0x1000 == 0
        &&& self.kernel_fs_end % 0x1000 == 0
        &&& self.platform_type == 0x0001 || self.platform_type == 0x0002
        &&& self.platform_type matches 0x0001 ==> self.vtom != 0
    }
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
        &&& self.platform_type.is_constant()
    }
}

} // verus!
