use core::ptr::eq;

use deko_macros::DekoDebug;
use deko_std::array::Array;
use deko_std::boot::{ACPITableBuffer, RSDPDesc};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::collections::{update_vec, Vec};
use crate::{die, kerror, kinfo, kpanic_if, kunimplemented};

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
        kinfo!("FW_CFG has", n, "files");

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
                if terminated || c == 0 || (c < 0 || c >= 128) {
                    terminated = true;
                } else {
                    name.update(j, c);
                }
            }

            kinfo!("\tFW_CFG file:", i, "name:", name.as_str());

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
#[verus_spec()]
pub fn load_acpi_tables<'a>() -> Option<ACPITableBuffer<'a>> {
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
            kinfo!("rsdp=>", rsdp);  // RSD PTR + BOCHS signature

            let addr = rsdp.rsdt_address as usize;
            // now we've got the offset.
            // Now we need to have many dangerous raw pointer operations here.
            // todo....
        }
        return None;
    }
    None
}

} // verus!
