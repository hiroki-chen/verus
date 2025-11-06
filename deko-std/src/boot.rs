use vstd::invariant;
use vstd::prelude::*;

use crate::prelude::*;

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

#[allow(non_camel_case_types)]
#[repr(u16)]
#[derive(Clone)]
pub enum MemoryMapEntryType {
    /// Normal memory.
    MEMORY = 0x0,
    /// Platform reserved memory.
    PLATFORM_RESERVED = 0x1,
    /// Persistent memory (PMEM).
    PERSISTENT = 0x2,
    /// Memory where VTL2 protections that deny access to lower VTLs can be
    /// applied. Some isolation architectures only allow VTL2 protections on
    /// certain memory ranges.
    VTL2_PROTECTABLE = 0x3,
    /// Specific Purpose memory (SPM). This is memory with special properties
    /// reserved for specific purposes and shouldn't be used by the firmware
    /// or operating system. This corresponds with the UEFI memory map entry
    /// flag EFI_MEMORY_SP, introduced in UEFI 2.8.
    /// See https://uefi.org/specs/UEFI/2.10/07_Services_Boot_Services.html
    SPECIFIC_PURPOSE = 0x4,
    /// Hidden memory is visible in the memory map but is hidden from any other
    /// enumeration that may be used to expose available memory to the VM.
    HIDDEN = 0x5,
}

#[repr(C)]
#[derive(Clone)]
pub struct IgvmVhsMemoryMapEntry {
    /// The starting gpa page number for this range of memory.
    pub starting_gpa_page_number: u64,
    /// The number of pages in this range of memory.
    pub number_of_pages: u64,
    /// The type of memory this entry represents.
    pub entry_type: MemoryMapEntryType,
    /// Flags about this memory entry.
    pub flags: u16,
    /// Reserved.
    pub reserved: u32,
}

#[derive(Clone)]
#[repr(C, align(64))]
pub struct IgvmMemoryMap {
    memory_map: Array<IgvmVhsMemoryMapEntry, 0xAA>,
}

#[repr(C)]
#[derive(Default)]
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

impl Constant for HeaderRaw {
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

/// An entry that represents an area of pre-validated memory defined by the
/// firmware in the IGVM file.
#[repr(C, packed)]
#[derive(Clone, Copy, Default)]
pub struct IgvmParamBlockFwMem {
    /// The base physical address of the prevalidated memory region.
    pub base: u32,
    /// The length of the prevalidated memory region in bytes.
    pub size: u32,
}

/// The portion of the IGVM parameter block that describes metadata about
/// the firmware image embedded in the IGVM file.
#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct IgvmParamBlockFwInfo {
    /// The guest physical address of the start of the guest firmware. The
    /// permissions on the pages in the firmware range are adjusted to the guest
    /// VMPL. If this field is zero then no firmware is launched after
    /// initialization is complete.
    pub start: u32,
    /// The size of the guest firmware in bytes. If the firmware size is zero then
    /// no firmware is launched after initialization is complete.
    pub size: u32,
    /// Indicates that the initial location of firmware is at the base of
    /// memory and will not be loaded into the ROM range.
    pub in_low_memory: u8,
    #[doc(hidden)]
    pub _reserved: [u8; 7],
    /// The guest physical address at which the firmware expects to find the
    /// secrets page.
    pub secrets_page: u32,
    /// The guest physical address at which the firmware expects to find the
    /// calling area page.
    pub caa_page: u32,
    /// The guest physical address at which the firmware expects to find the
    /// CPUID page.
    pub cpuid_page: u32,
    /// The guest physical address of the IGVM memory map consumed by the
    /// guest firmware.
    pub memory_map_page: u32,
    /// The number of pages reserved for the IGVM memory map consumed by the
    /// guest firmware.
    pub memory_map_page_count: u32,
    /// The number of prevalidated memory regions defined by the firmware.
    pub prevalidated_count: u32,
    /// The prevalidated memory regions defined by the firmware.
    // pub prevalidated: [IgvmParamBlockFwMem; 8],
    pub prevalidated: Array<IgvmParamBlockFwMem, 8>,
}

/// The IGVM parameter block is a measured page constructed by the IGVM file
/// builder which describes where the additional IGVM parameter information
/// has been placed into the guest address space.
#[repr(C, packed)]
pub struct IgvmParamBlock {
    /// The total size of the parameter area, beginning with the parameter
    /// block itself and including any additional parameter pages which follow.
    pub param_area_size: u32,
    /// The offset, in bytes, from the base of the parameter block to the base
    /// of the parameter page.
    pub param_page_offset: u32,
    /// The offset, in bytes, from the base of the parameter block to the base
    /// of the host-supplied MADT.
    pub madt_offset: u32,
    /// The size, in bytes, of the MADT area.
    pub madt_size: u32,
    /// The offset, in bytes, from the base of the parameter block to the base
    /// of the memory map (which is in IGVM format).
    pub memory_map_offset: u32,
    /// The offset, in bytes, of the guest context, or zero if no guest
    /// context is present.
    pub guest_context_offset: u32,
    /// The port number of the serial port to use for debugging.
    pub debug_serial_port: u16,
    /// Indicates whether the guest can support alternate injection.
    pub use_alternate_injection: u8,
    /// Indicates whether SVSM should suppress interrupts when running on SEV-SNP.
    pub suppress_svsm_interrupts_on_snp: u8,
    /// Indicates whether SVSM can assume that the qemu testdev device exists to assist testing.
    pub has_qemu_testdev: u8,
    /// Indicates whether SVSM should use an IO port to read the qemu FwCfg.
    pub has_fw_cfg_port: u8,
    /// Indicates whether SVSM can use "IORequest"s to assist with testing.
    pub has_test_iorequests: u8,
    #[doc(hidden)]
    pub _reserved: [u8; 1],
    /// Metadata containing information about the firmware image embedded in the
    /// IGVM file.
    pub firmware: IgvmParamBlockFwInfo,
    /// The number of bytes for the stage1 bootloader
    pub stage1_size: u32,
    #[doc(hidden)]
    pub _reserved2: u32,
    /// The guest physical address of the base of the stage1 bootloader
    pub stage1_base: u64,
    /// The amount of space that must be reserved at the base of the kernel
    /// memory region (e.g. for VMSA contents).
    pub kernel_reserved_size: u32,
    /// The guest physical address of the base of the kernel memory region.
    pub kernel_base: u64,
    /// The minimum size to allocate for the kernel in bytes. If the hypervisor supplies a memory
    /// region in the memory map that starts at kernel_base and is larger, that size will be used
    /// instead.
    pub kernel_min_size: u32,
    /// The maximum size to allocate for the kernel in bytes. If the hypervisor supplies a memory
    /// region in the memory map that starts at kernel_base and is larger, this maximum size will
    /// be used instead.
    pub kernel_max_size: u32,
    /// The value of vTOM used by the guest, or zero if not used.
    pub vtom: u64,
}

impl WellFormed for IgvmParamBlock {
    open spec fn wf(&self) -> bool {
        &&& self.debug_serial_port + 8 <= u16::MAX
    }
}

impl WellFormed for IgvmParamBlockFwInfo {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for IgvmParamBlockFwMem {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for IgvmVhsMemoryMapEntry {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl WellFormed for IgvmMemoryMap {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl IgvmParamBlock {
    pub uninterp spec fn find_kernel_region_spec(&self) -> Option<(PhysAddr, PhysAddr)>;

    /// Find the kernel memory region defined by the IGVM parameters.
    #[verifier::external_body]
    pub fn find_kernel_region(&self) -> (r: Option<(PhysAddr, PhysAddr)>)
        requires
            self.wf(),
        ensures
            r matches Some((start, end)) ==> {
                &&& start.wf()
                &&& end.wf()
                &&& start@ <= end@
                &&& start@ % PAGE_SIZE == 0
                &&& end@ % PAGE_SIZE == 0
                &&& end@ < u32::MAX
            },
            r == self.find_kernel_region_spec(),
    {
        let kernel_base = self.kernel_base;
        let mut kernel_size = self.kernel_min_size;

        // Check the untrusted hypervisor-provided memory map to see if the size of the kernel
        // should be adjusted.
        let igvm_mmap = unsafe {
            &*((self as *const IgvmParamBlock as u64).checked_add(
                self.memory_map_offset as u64,
            )? as *const IgvmMemoryMap)
        };

        let mut i = 0;
        while i < 0xAA
            invariant
                i <= 0xAA,
                self.wf(),
            decreases 0xAA - i,
        {
            let e = igvm_mmap.memory_map.index(i);
            if let MemoryMapEntryType::HIDDEN = e.entry_type {
                let region_size_bytes = e.number_of_pages.try_into().unwrap_or(
                    u32::MAX,
                ).saturating_mul(PAGE_SIZE as u32);
                kernel_size = region_size_bytes.clamp(self.kernel_min_size, self.kernel_max_size);

                break ;
            }
            i += 1;
        }

        Some(
            (
                PhysAddr::from(kernel_base),
                PhysAddr::from(kernel_base.checked_add(kernel_size as u64)?),
            ),
        )
    }
}

} // verus!
