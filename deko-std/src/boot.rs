use deko_macros::DekoDebug;
use vstd::invariant;
use vstd::prelude::*;

use crate::prelude::*;

verus! {

pub broadcast axiom fn axiom_meta_array_size_wf()
    ensures
        #[trigger] Array::<ACPITableMeta, 8>::size_wf(),
;

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
#[derive(Clone, DekoDebug)]
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

#[derive(Clone, Copy, DekoDebug)]
#[repr(C, packed)]
pub struct MADTEntryHeader {
    pub entry_type: u8,
    pub entry_len: u8,
}

/// Entry for a local APIC within MADT
#[derive(Clone, DekoDebug)]
#[repr(C, packed)]
struct MADTEntryLocalApic {
    header: MADTEntryHeader,
    acpi_id: u8,
    apic_id: u8,
    flags: u32,
}

/// Entry for a local X2APIC within MADT
#[derive(Clone, Copy, DekoDebug)]
#[repr(C, packed)]
struct MADTEntryLocalX2Apic {
    header: MADTEntryHeader,
    reserved: Array<u8, 2>,
    apic_id: u32,
    flags: u32,
    acpi_id: u32,
}

/// Higher level representation of the raw ACPI table header
#[derive(Clone, Copy, DekoDebug)]
#[repr(C, packed)]
pub struct ACPITableHeader {
    pub sig: Array<u8, 4>,
    pub len: u32,
    pub rev: u8,
    pub chksum: u8,
    pub oem_id: Array<u8, 6>,
    pub oem_table_id: Array<u8, 8>,
    pub oem_rev: u32,
    pub compiler_id: Array<u8, 4>,
    pub compiler_rev: u32,
}

#[derive(DekoDebug)]
pub struct ACPITable<'a> {
    pub header: ACPITableHeader,
    /// Raw binary content of ACPI table
    pub buf: &'a [u8],
}

impl<'a> ACPITable<'a> {
    /// Try to parse a raw ACPI table from the given address.
    #[verifier::external_body]
    pub fn new(buf: &[u8]) -> (r: Self)
        ensures
            r.wf(),
    {
        let ptr = buf.as_ptr();
        let header = unsafe { &*(ptr as *const ACPITableHeader) };
        let len = header.len as usize;

        let buf = unsafe {
            core::slice::from_raw_parts(
                ptr.add(core::mem::size_of::<ACPITableHeader>()) as *const u8,
                len,
            )
        };

        ACPITable { header: header.clone(), buf }
    }

    /// Try to parse the raw bytes as a CPU topology table. Since this
    /// requires some unsafe code, we mark it as external body.
    #[cfg(feature = "alloc")]
    #[verifier::external_body]  // remove this...
    pub fn get_cpu_topology<A: core::alloc::Allocator + WellFormed>(&self, alloc: A) -> (r: Option<
        alloc::vec::Vec<ACPICPUInfo, A>,
    >)
        requires
            self.wf(),
            alloc.wf(),
        ensures
            r matches Some(cpus) ==> {
                forall|i: int|
                    #![trigger cpus@[i]]
                    0 <= i < cpus@.len() ==> (
                    cpus@[i]).enabled
                // perhaps need to reason about id boundaries.

            },
    {
        use alloc::vec::Vec;

        let mut cpus: Vec<ACPICPUInfo, A> = Vec::new_in(alloc);
        let mut offset = 8;  // Skip the MADT header which is 8 bytes

        while offset < self.buf.len() {
            let entry = unsafe { &*(self.buf.as_ptr().add(offset) as *const MADTEntryHeader) };

            match entry.entry_type {
                // We have encountered a Processor Local APIC entry
                0 if entry.entry_len == 8 => {
                    let lapic_entry = unsafe {
                        &*(self.buf.as_ptr().add(offset) as *const MADTEntryLocalApic)
                    };
                    let cpu_info = ACPICPUInfo {
                        apic_id: lapic_entry.apic_id as u32,
                        enabled: (lapic_entry.flags & 0x1) != 0,
                    };
                    cpus.push(cpu_info);
                    offset += entry.entry_len as usize;
                }
                // We have encountered a Processor Local x2APIC entry
                ,
                9 if entry.entry_len == 16 => {
                    let x2apic_entry = unsafe {
                        &*(self.buf.as_ptr().add(offset) as *const MADTEntryLocalX2Apic)
                    };
                    let cpu_info = ACPICPUInfo {
                        apic_id: x2apic_entry.apic_id,
                        enabled: (x2apic_entry.flags & 0x1) != 0,
                    };
                    cpus.push(cpu_info);
                    offset += entry.entry_len as usize;
                },
                _ => {
                    // Unknown.
                    offset += entry.entry_len as usize;
                },
            }
        }

        Some(cpus)
    }
}

impl WellFormed for ACPITableHeader {
    open spec fn wf(&self) -> bool {
        &&& self.sig.wf()
    }
}

impl<'a> WellFormed for ACPITable<'a> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.header.wf()
    }
}

// #[derive(DekoDebug)]
#[cfg(feature = "alloc")]
#[verifier::reject_recursive_types(A)]
pub struct ACPITableBuffer<A: core::alloc::Allocator + WellFormed> {
    pub buf: alloc::vec::Vec<u8, A>,
    /// Collection of metadata for ACPI tables, including signatures
    pub tables: Array<ACPITableMeta, 8>,  // Max 8 tables
}

impl WellFormed for ACPITableMeta {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.sig.wf()
    }
}

#[cfg(feature = "alloc")]
impl<A: core::alloc::Allocator + WellFormed> WellFormed for ACPITableBuffer<A> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.tables.wf()
    }
}

/// Root System Description Pointer (RSDP) structure for ACPI 2.0+.
#[derive(DekoDebug, Clone, Copy)]
#[repr(C, packed)]
pub struct RSDPDesc {
    /// Signature must contain "RSD PTR"
    pub sig: Array<u8, 8>,
    /// Checksum to add to all other bytes
    pub chksum: u8,
    /// OEM-supplied string
    pub oem_id: Array<u8, 6>,
    /// Revision of the ACPI
    pub rev: u8,
    /// Physical address of the RSDT
    pub rsdt_addr: u32,
}

#[derive(DekoDebug, Clone, Copy)]
pub struct ACPITableMeta {
    /// 4-character signature of the table
    pub sig: Array<u8, 4>,
    /// The offset of the table within the table buffer
    pub offset: usize,
}

#[repr(C)]
#[derive(Clone, DekoDebug)]
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

/// The IGVM parameter page is an unmeasured page containing individual
/// parameters that are provided by the host loader.
#[repr(C, packed)]
#[derive(Clone, DekoDebug)]
pub struct IgvmParamPage {
    /// The number of vCPUs that are configured for the guest VM.
    pub cpu_count: u32,
    /// The environment informatiom supplied to describe the execution
    /// environment.  This is defined as a u32 and is converted to an
    /// IgvmEnvironmentInfo when it is used.
    pub environment_info: u32,
}

#[repr(C, align(64))]
#[derive(DekoDebug)]
pub struct IgvmMemoryMap {
    memory_map: Array<IgvmVhsMemoryMapEntry, 0xAA>,
}

#[repr(C, packed)]
#[derive(DekoDebug)]
pub struct IgvmGuestContext {
    pub cr0: u64,
    pub cr3: u64,
    pub cr4: u64,
    pub efer: u64,
    pub gdt_base: u64,
    pub gdt_limit: u32,
    pub code_selector: u16,
    pub data_selector: u16,
    pub rip: u64,
    pub rax: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbx: u64,
    pub rsp: u64,
    pub rbp: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,
}

#[derive(DekoDebug)]
pub struct IgvmParams<'a> {
    pub igvm_param_block: &'a IgvmParamBlock,
    pub igvm_param_page: &'a IgvmParamPage,
    pub igvm_memory_map: &'a IgvmMemoryMap,
    pub igvm_madt: Option<&'a [u8]>,
    pub igvm_guest_context: Option<&'a IgvmGuestContext>,
}

#[repr(C)]
#[derive(Default, DekoDebug)]
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
#[derive(Clone, Copy, Default, DekoDebug)]
pub struct IgvmParamBlockFwMem {
    /// The base physical address of the prevalidated memory region.
    pub base: u32,
    /// The length of the prevalidated memory region in bytes.
    pub size: u32,
}

/// The portion of the IGVM parameter block that describes metadata about
/// the firmware image embedded in the IGVM file.
#[repr(C, packed)]
#[derive(Copy, Clone, DekoDebug)]
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
    /// Indicates that the memory map provided by the firmware is prevalidated
    pub mmap_prevalidated: u8,
    #[doc(hidden)]
    pub _reserved: [u8; 6],
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
#[derive(DekoDebug)]
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
        &&& self.param_area_size as u64 % PAGE_SIZE == 0
        &&& self.param_area_size != 0
        &&& self.firmware.wf()
    }
}

impl WellFormed for IgvmParamBlockFwInfo {
    open spec fn wf(&self) -> bool {
        &&& self.size as u64 % PAGE_SIZE == 0
        &&& (self.size != 0 ==> self.start as u64 % PAGE_SIZE == 0)
        &&& self.secrets_page as u64 % PAGE_SIZE == 0
        &&& self.cpuid_page as u64 % PAGE_SIZE == 0
        &&& self.caa_page as u64 % PAGE_SIZE == 0
        &&& self.memory_map_page as u64 % PAGE_SIZE == 0
        &&& self.memory_map_page_count as u64 % PAGE_SIZE == 0
        &&& self.secrets_page <= 0x8000_0000
        &&& self.cpuid_page <= 0x8000_0000
        &&& self.caa_page <= 0x8000_0000
        &&& self.memory_map_page + self.memory_map_page_count <= 0x8000_0000
        &&& forall|i: int|
            #![trigger self.prevalidated@[i]]
            0 <= i < self.prevalidated_count as int ==> {
                let start = self.prevalidated@[i].base as u64;
                let end = start + self.prevalidated@[i].size as u64;

                // All pages should not overlap
                &&& self.secrets_page as u64 + PAGE_SIZE <= start || end <= self.secrets_page as u64
                &&& self.cpuid_page as u64 + PAGE_SIZE <= start || end <= self.cpuid_page as u64
                &&& self.caa_page as u64 + PAGE_SIZE <= start || end <= self.caa_page as u64
                &&& self.memory_map_page as u64 + (self.memory_map_page_count as u64 * PAGE_SIZE)
                    <= start || end <= self.memory_map_page as u64
            }
        &&& self.prevalidated_count as usize <= self.prevalidated@.len() as usize
        &&& Array::<IgvmParamBlockFwMem, 8>::size_wf()
        &&& self.prevalidated.wf()
        &&& forall|i: int|
            #![trigger self.prevalidated@[i]]
            0 <= i < self.prevalidated_count as int ==> self.prevalidated@[i].wf()
        &&& forall|i: int, j: int|
            #![trigger self.prevalidated@[i], self.prevalidated@[j]]
            0 <= i < self.prevalidated_count as int && 0 <= j < self.prevalidated_count as int && i
                != j ==> self.prevalidated@[i].base + self.prevalidated@[i].size
                <= self.prevalidated@[j].base || self.prevalidated@[j].base
                + self.prevalidated@[j].size <= self.prevalidated@[i].base
    }
}

impl WellFormed for IgvmParamBlockFwMem {
    open spec fn wf(&self) -> bool {
        &&& self.base as u64 % PAGE_SIZE == 0
        &&& self.size as u64 % PAGE_SIZE == 0
        &&& self.size != 0
        &&& self.base + self.size <= 0x000f_ffff_ffff_f000u64
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

#[derive(Clone, DekoDebug)]
pub struct ACPICPUInfo {
    /// The APIC ID for the CPU
    pub apic_id: u32,
    /// Indicates whether the CPU is enabled
    pub enabled: bool,
}

impl WellFormed for ACPICPUInfo {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl<'a> IgvmParams<'a> {
    #[inline]
    pub fn size(&self) -> usize
        returns
            self.igvm_param_block.param_area_size as usize,
    {
        // Calculate the total size of the parameter area.  The
        // parameter area always begins at the kernel base
        // address.
        self.igvm_param_block.param_area_size as usize
    }

    /// Probe the topology information from the MADT, if present.
    #[cfg(feature = "alloc")]
    pub fn load_cpu_info<A: core::alloc::Allocator + WellFormed>(&self, alloc: A) -> Option<
        alloc::vec::Vec<ACPICPUInfo, A>,
    >
        requires
            self.wf(),
            alloc.wf(),
    {
        match self.igvm_madt {
            Some(madt_data) if madt_data.len() != 0 => {
                let acpi = ACPITable::new(madt_data);

                acpi.get_cpu_topology(alloc)
            },
            // If no madt is found then we will let the caller handle it.
            _ => None,
        }
    }
}

impl<'a> WellFormed for IgvmParams<'a> {
    open spec fn wf(&self) -> bool {
        &&& self.igvm_param_block.wf()
    }
}

} // verus!
