use core::ptr::eq;

use deko_macros::DekoDebug;
use deko_std::address::PaddrRange;
use deko_std::array::Array;
use deko_std::boot::{
    ACPICPUInfo, ACPITable, ACPITableBuffer, ACPITableHeader, ACPITableMeta, IgvmParams, RSDPDesc,
    LOWMEM_END,
};
use deko_std::prelude::{create_paddr_range, PhysAddr, PAGE_SIZE};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::collections::{update_vec, Vec};
use crate::cpu::DekoCpuCtx;
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::mm::paging::PageTablePermission;
use crate::mm::vm::TempMapping;
use crate::{die, kerror, kinfo, kpanic_if, kunimplemented, kwarn, vec, DekoKernelLaunchInfo};

verus! {

broadcast axiom fn axiom_name_array_size_wf()
    ensures
        #[trigger] Array::<u8, 56>::size_wf(),
;

pub const APIC_SIG: &'static str = "APIC";

pub const APIC_PATH: &'static str = "etc/acpi/tables";

pub const RSDP_PATH: &'static str = "etc/acpi/rsdp";

pub const FW_CFG_PORT_SEL: u16 = 0x510;

pub const FW_CFG_PORT_DATA: u16 = 0x511;

pub const FW_CFG_PORT_DMA: u16 = 0x512;

pub const FW_CFG_SIGNATURE: u16 = 0x0000;

pub const FW_CFG_ID: u16 = 0x0001;

pub const FW_CFG_FILE_DIR: u16 = 0x0019;

pub struct FwCfg;

#[verus_verify]
impl FwCfg {
    pub fn fwcfg_probe(&self) -> bool {
        self.select(FW_CFG_SIGNATURE);

        let b1 = crate::imp::inb(FW_CFG_PORT_DATA);
        let b2 = crate::imp::inb(FW_CFG_PORT_DATA);
        let b3 = crate::imp::inb(FW_CFG_PORT_DATA);
        let b4 = crate::imp::inb(FW_CFG_PORT_DATA);

        [b1, b2, b3, b4] == ['Q' as u8, 'E' as u8, 'M' as u8, 'U' as u8]
    }

    /// Selects a firmware configuration item for subsequent access.
    #[inline]
    pub fn select(&self, cfg: u16) {
        crate::imp::outw(FW_CFG_PORT_SEL, cfg);
    }

    #[inline]
    pub fn read_byte(&self) -> u8 {
        crate::imp::inb(FW_CFG_PORT_DATA)
    }

    #[inline]
    pub fn read_bytes(&self, buf: &mut Vec<u8>) {
        let len = buf.len();
        for i in 0..len
            invariant
                i <= len,
                len == buf@.len(),
        {
            update_vec(buf, i, self.read_byte());
        }
    }

    #[inline]
    pub fn read_word_be(&self) -> u16 {
        let b1 = crate::imp::inb(FW_CFG_PORT_DATA) as u16;
        let b2 = crate::imp::inb(FW_CFG_PORT_DATA) as u16;
        (b1 << 8) | b2
    }

    #[inline]
    pub fn read_dword_be(&self) -> u32 {
        let b1 = crate::imp::inb(FW_CFG_PORT_DATA) as u32;
        let b2 = crate::imp::inb(FW_CFG_PORT_DATA) as u32;
        let b3 = crate::imp::inb(FW_CFG_PORT_DATA) as u32;
        let b4 = crate::imp::inb(FW_CFG_PORT_DATA) as u32;

        (b1 << 24) | (b2 << 16) | (b3 << 8) | b4
    }

    pub fn select_file(&self, target: &str) -> Option<FwCfgFile> {
        self.select(FW_CFG_FILE_DIR);
        let n = self.read_dword_be();

        if n >= 0x1000 {
            kerror!("Too many FW_CFG files:", n);
            return None;
        }
        let mut i = 0;
        #[verus_spec(
            invariant
                i <= n,
            decreases
                n - i,
        )]
        while i < n {
            broadcast use axiom_name_array_size_wf;

            let size = self.read_dword_be();
            let select = self.read_word_be();
            let reserved = self.read_word_be();
            let mut name = Array::<u8, 56>::fill(0);
            let mut terminated = false;
            for j in 0..56
                invariant
                    j <= 56,
                    name.wf(),
                    forall|k: int| 0 <= k < name@.len() ==> 0 <= #[trigger] name@[k] < 128,
            {
                let c = self.read_byte();
                if terminated || c == 0 || c >= 128 {
                    terminated = true;
                } else {
                    name.update(j, c);
                }
            }

            // Need to more be specific about what `eq` we want here.
            if <str as PartialEq>::eq(name.as_str().trim_end_matches('\0'), target) {
                kinfo!("Found FW_CFG target file:", target);

                return Some(FwCfgFile { size, select, reserved, name });
            }
            i += 1;
        }

        None
    }
}

#[derive(DekoDebug, Clone, Copy)]
pub struct FwCfgFile {
    pub size: u32,
    pub select: u16,
    pub reserved: u16,
    pub name: Array<u8, 56>,
}

#[non_exhaustive]
#[derive(DekoDebug, Clone, Copy)]
#[repr(u16)]
pub enum FwCfgCtl {
    FwCtlError = 1,
    FwCtlRead = 2,
    FwCtlSkip = 4,
    FwCtlSelect = 8,
    FwCtlWrite = 16,
}

pub struct FwCfgDmaAccess {
    pub control: u32,
    pub length: u32,
    pub address: u64,
}

#[verifier::external_body]
pub fn loads_rsdp<'a>() -> Option<RSDPDesc> {
    let fw = FwCfg {  };
    kpanic_if!(!fw.fwcfg_probe(), "FW_CFG not detected");  // this is fatal error.

    if let Some(rsdp) = FwCfg.select_file(RSDP_PATH) {
        kinfo!("Loading RSDP from firmware configuration:", RSDP_PATH);

        let filesize = rsdp.size as usize;
        let mut buffer = crate::vec![0u8; filesize];

        kinfo!("Transferring", filesize, "bytes via FW_CFG");
        kinfo!("Selecting", rsdp.select, "for read");
        // Select the file.
        fw.select(rsdp.select);
        fw.read_bytes(&mut buffer);

        kinfo!("Successfully read raw RSDP from FW_CFG");

        Some(unsafe { core::ptr::read(buffer.as_ptr() as *const RSDPDesc) })
    } else {
        None
    }
}

/// Loads the ACPI tables via the firmware interfaces.
///
/// Note that for virtualized environments like SNP guests,
/// the ACPI tables may need to be loaded via emulator provided
/// IO ports.
///
/// See [this](https://wiki.osdev.org/QEMU_fw_cfg).
///
/// Sometimes the emulator will lack some information necessary to
/// configure the guest system. In such cases, the guest firmware
/// need to provide extra information via the following command:
///
/// ```sh
/// -fw_cfg name=/etc/acpi/tables,file=acpi_tables.bin \
/// -fw_cfg name=/foo/bar/baz,file=aux.bin
/// ```
///
/// If the guest image is packed via IGVM then the firmware
/// must be specified in the IGVM config file via the `--firmware`
/// option. This file is usually the OVMF firmware image:
///
/// ```sh
/// igvmbuilder --firmware /path/to/OVMF_CODE.fd ...
///
/// qemu_system_x86_64 -object igvm-cfg,id=igvm,file=xxx.igvm ...
/// ```
#[cfg(feature = "alloc")]
#[verus_spec(r =>
    ensures
        r.wf(),
)]
pub fn load_acpi_tables() -> Option<ACPITableBuffer<DekoAllocatorApi>> {
    use crate::kdebug;

    broadcast use deko_std::boot::axiom_meta_array_size_wf;

    let fw = FwCfg {  };
    kpanic_if!(!fw.fwcfg_probe(), "FW_CFG not detected");  // this is fatal error.

    if let Some(acpi) = FwCfg.select_file(APIC_PATH) {
        kinfo!("Loading ACPI tables from firmware configuration:", APIC_PATH);

        let filesize = acpi.size as usize;
        let mut buffer = crate::vec![0u8; filesize];

        kinfo!("Transferring", filesize, "bytes via FW_CFG");
        kinfo!("Selecting", acpi.select, "for read");
        // Select the file.
        fw.select(acpi.select);
        fw.read_bytes(&mut buffer);

        kinfo!("Successfully read raw ACPI tables from FW_CFG");

        // return Some(ACPITableBuffer::new(&buffer));
        if let Some(rsdp) = loads_rsdp() {
            kinfo!("Successfully loaded RSDP from FW_CFG");

            let addr = rsdp.rsdt_addr as usize;
            // now we've got the offset.
            // Now we need to have many dangerous raw pointer operations here.
            let rsdp = read_acpi_table(&buffer, addr)?;
            if rsdp.buf.len() % core::mem::size_of::<u32>() != 0 {
                kerror!("RSDT length is not multiple of 4:", rsdp.buf.len());
                return None;
            }
            let rsdp_offsets_arr_len = rsdp.buf.len() / core::mem::size_of::<u32>();
            if rsdp_offsets_arr_len > 8 {
                kerror!("Too many ACPI tables:", rsdp_offsets_arr_len);
                return None;
            }
            kdebug!("rsdp =>", rsdp);  // RSD PTR + BOCHS signature
            assume(Array::<u8, 4>::size_wf());
            let mut i = 0;
            let mut tables = Array::<ACPITableMeta, 8>::fill(
                ACPITableMeta { sig: Array::<u8, 4>::fill(0), offset: 0 },
            );

            #[verus_spec(
                 invariant
                    i <= rsdp_offsets_arr_len <= 8,
                    rsdp.buf@.len() % (core::mem::size_of::<u32>() as nat) == 0,
                    core::mem::size_of::<u32>() == 4,
                    rsdp_offsets_arr_len == rsdp.buf.len() / core::mem::size_of::<u32>(),
                    tables.wf(),
                    tables@.len() == 8,
                decreases
                    rsdp_offsets_arr_len - i,
            )]
            while i < rsdp_offsets_arr_len {
                let b1 = rsdp.buf[i * 4 + 0] as u32;
                let b2 = rsdp.buf[i * 4 + 1] as u32;
                let b3 = rsdp.buf[i * 4 + 2] as u32;
                let b4 = rsdp.buf[i * 4 + 3] as u32;

                // little endian
                let offset = (b1) | (b2 << 8) | (b3 << 16) | (b4 << 24);
                let this_table_hdr = read_acpi_table(&buffer, offset as usize)?.header;

                kdebug!("Read ACPI Table at offset", offset, "header:", this_table_hdr);
                // Now we just read the meta.
                tables.update(
                    i,
                    ACPITableMeta { sig: this_table_hdr.sig, offset: offset as usize },
                );

                i += 1;
            }

            return Some(ACPITableBuffer { buf: buffer, tables });
        }
        return None;
    }
    None
}

/// Given a raw buffer of the ACPI tables, read the table at the given offset.
///
/// Note that this does not parse the body of the table.
#[verifier::external_body]
#[verus_spec(r =>
    ensures
        r.wf(),
)]
pub fn read_acpi_table(buf: &[u8], offset: usize) -> Option<ACPITable> {
    if offset + core::mem::size_of::<ACPITable>() > buf.len() {
        return None;
    }
    let hdr = {
        unsafe {
            // Possibly unaligned read.
            core::ptr::read_unaligned(buf.as_ptr().add(offset) as *const ACPITableHeader)
        }
    };

    let content = &buf[offset + core::mem::size_of::<ACPITableHeader>()..offset + (
    hdr.len as usize)];

    Some(ACPITable { header: hdr, buf: content })
}

/// Find scattered firmware regions from the IGVM parameters.
#[verus_spec(r =>
    requires
        igvm_params.wf(),
    ensures
        forall |i: int|
        #![trigger r@[i]]
        0 <= i < r@.len() ==> {
            &&& r@[i].wf()
            &&& r@[i].start.0 <= r@[i].end.0
            &&& r@[i].start@ % PAGE_SIZE == 0
            &&& r@[i].end@ % PAGE_SIZE == 0
            &&& r@[i].end.0 < 0x000f_ffff_ffff_f000u64
        }
)]
pub fn get_fw_regions_from_igvm(igvm_params: &IgvmParams<'_>) -> Vec<PaddrRange> {
    let mut v: Vec<PaddrRange> = vec![];
    let fw_is_in_low_mem = igvm_params.igvm_param_block.firmware.in_low_memory != 0;
    let start = igvm_params.igvm_param_block.firmware.start as u64;
    let size = igvm_params.igvm_param_block.firmware.size as u64;
    let map_start = igvm_params.igvm_param_block.firmware.memory_map_page as u64;
    let map_size = igvm_params.igvm_param_block.firmware.memory_map_page_count as u64;

    // Do extra care if the firmware is in low memory.
    if fw_is_in_low_mem {
        v.push(PaddrRange { start: PhysAddr(0), end: PhysAddr(LOWMEM_END as u64) });
    }
    // Push the fw_region into the vector.

    if size != 0 {
        v.push(PaddrRange { start: PhysAddr(start), end: PhysAddr(start + size) });
    }
    // If this firmware expects an IGVM memory map but the IGVM memory
    // map is not within any of the firmware GPA ranges, then add the IGVM
    // memory map to the set of firmware regions.

    if igvm_params.igvm_param_block.firmware.memory_map_page_count != 0 {
        let map_region = PaddrRange {
            start: PhysAddr(map_start),
            end: PhysAddr(map_start + map_size),
        };

        // Check if map_region is within any existing region.
        if map_region.end.0 <= LOWMEM_END as _ {
            v.push(map_region);
        } else if map_region.start.0 >= start && map_region.end.0 <= start + size {
            v.push(map_region);
        }
    }
    v
}

/// Invalidates the early-boot memory ranges that were used by the firmware.
/// This keeps the system’s RMP state consistent while allowing those pages to be
/// reclaimed later by the frame allocator.
///
/// # Notes
/// - This function intentionally does **not** track or restore pages that may
///   need to be re-validated at later boot stages. Any pages invalidated here
///   are expected to be re-validated on demand when they are actually reused.
/// - “Old memory” and “firmware memory” ranges may overlap (e.g., when the IGVM
///   loader places firmware into low memory). To avoid duplicating overlap checks,
///   we allow overlap here and handle correctness in later validation.
///
/// # Interaction with later validation
/// In a later stage, [`crate::imp::validate_fw_memories`] performs the
/// authoritative validation of firmware-occupied regions. If a page invalidated
/// here is later (re-)validated (e.g., by a frame allocation path), then
/// [`crate::imp::validate_fw_memories`] will detect the mismatch and panic.
/// In that case, no page state change should occur.
#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
    requires
        header.wf(),
        igvm_params.wf(),
        old(pgtable_perm).wf(),
    ensures
        final(pgtable_perm).wf(),
        final(pgtable_perm).pgtable_perm == old(pgtable_perm).pgtable_perm,
        final(pgtable_perm).private_bit == old(pgtable_perm).private_bit,
        final(pgtable_perm).shared_bit == old(pgtable_perm).shared_bit,
        final(pgtable_perm).mapping_space == old(pgtable_perm).mapping_space,
)]
pub fn invalidate_early_boot_mem(header: &DekoKernelLaunchInfo, igvm_params: &IgvmParams<'_>) {
    let need_psc = igvm_params.igvm_param_page.environment_info & 0x1 != 0;

    // The firmware might use the low memory regions so we need to
    // invalidate them before usage so as to avoid any extra RMP faults later.
    if igvm_params.igvm_param_block.firmware.in_low_memory == 0 {
        kinfo!("Invalidating low memory used by firmware [0x0 - 0x", LOWMEM_END => hex , ")");

        proof_with!(Tracked(pgtable_perm));
        invalidate_boot_memory(
            header,
            PaddrRange { start: PhysAddr(0), end: PhysAddr(LOWMEM_END as u64) },
            need_psc,
        );
    }
    proof_with!(Tracked(pgtable_perm));
    invalidate_boot_memory(
        header,
        PaddrRange {
            start: PhysAddr(header.stage2_start as u64),
            end: PhysAddr(header.stage2_end as u64),
        },
        need_psc,
    );

    kpanic_if!(header.kernel_elf_stage2_virt_end >= 0x000f_ffff_ffff_f000u64,
        "Invalid kernel ELF stage2 end address:", header.kernel_elf_stage2_virt_end);

    proof_with!(Tracked(pgtable_perm));
    invalidate_boot_memory(
        header,
        PaddrRange {
            start: PhysAddr(header.kernel_elf_stage2_virt_start as u64),  // 1 - 1 mapping.
            end: PhysAddr(header.kernel_elf_stage2_virt_end as u64),
        },
        need_psc,
    );

    if header.stage2_igvm_params_size != 0 {
        proof_with!(Tracked(pgtable_perm));
        invalidate_boot_memory(
            header,
            PaddrRange {
                start: PhysAddr(header.stage2_igvm_params_phys_addr as u64),
                end: PhysAddr(
                    header.stage2_igvm_params_phys_addr as u64
                        + header.stage2_igvm_params_size as u64,
                ),
            },
            need_psc,
        );
    }
}

/// Invalidates a specific boot memory range used by the firmware.
#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
    requires
        header.wf(),
        prange.wf(),
        old(pgtable_perm).wf(),
        prange.start@ % PAGE_SIZE == 0,
        prange.end@ % PAGE_SIZE == 0,
    ensures
        final(pgtable_perm).wf(),
        final(pgtable_perm).pgtable_perm == old(pgtable_perm).pgtable_perm,
        final(pgtable_perm).private_bit == old(pgtable_perm).private_bit,
        final(pgtable_perm).shared_bit == old(pgtable_perm).shared_bit,
        final(pgtable_perm).mapping_space == old(pgtable_perm).mapping_space,
)]
fn invalidate_boot_memory(header: &DekoKernelLaunchInfo, prange: PaddrRange, need_psc: bool) {
    kinfo!("Invalidating early memory region:", prange);

    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));

    let mut cur = prange.start.0;
    #[verus_spec(
        invariant
            prange.start@ <= cur <= prange.end@ < 0x000f_ffff_ffff_f000,
            prange.end@ % PAGE_SIZE == 0,
            prange.start@ % PAGE_SIZE == 0,
            cur@ % PAGE_SIZE == 0,
            prange.wf(),
            header.wf(),
            pgtable_perm.wf(),
            PAGE_SIZE == 0x1000,
        decreases
            prange.end@ - cur,
    )]
    while cur < prange.end.0 {
        let Some(mapping) = TempMapping::new(create_paddr_range(PhysAddr(cur), 1)) else {
            kerror!("Failed to create temporary mapping for paddr:", PhysAddr(cur),);
            die("");
        };

        assume(pgtable_perm.mapped(mapping.inner.start));

        let (r, changed) = crate::imp::pvalidate(
            mapping.inner.start.0,
            PAGE_SIZE,
            false,  // invalidate
            Tracked(pgtable_perm),
        );

        kpanic_if!(r != 0, "PVALIDATE failed to invalidate early boot memory at", PhysAddr(cur), "with return code", r);

        if !changed {
            // Not sure if we should instead treat this as a fatal error.
            kwarn!("Warning: PVALIDATE did not change page state when invalidating early boot memory at", PhysAddr(cur), "already invalid!");

            break ;
        }
        cur += PAGE_SIZE;
    }

    cpu.put(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);

    if need_psc {
        // Perform a PSC.
        crate::imp::page_state_change(prange, crate::imp::PageStateChangeOp::Shared);
    }
}

} // verus!
