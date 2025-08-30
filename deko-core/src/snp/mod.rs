use core::sync::atomic::AtomicU32;

use deko_meta::{HeaderRaw, Stage2LaunchInfo, LOWMEM_END};
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::address::{FixedAddressMappingRange, VirtAddr};
use crate::cpu::msr::read_msr;
use crate::hal::{PlatformApi, PlatformType};
use crate::mm::paging::PteFlags;
use crate::mm::{
    PageEncryptionMasks, FEATURE_MASK, MAX_PHYS_ADDR, PHYS_ADDR_SIZE, PTE_MASK_PRIVATE,
    PTE_MASK_SHARED,
};

pub mod snpcall;

#[cfg(feature = "logging")]
pub(crate) mod logging;

extern "C" {
    /// A global flag to indicate whether the AP has been started.
    static mut ap_flag: AtomicU32;
}

verus! {

fn has_vtom() -> bool {
    let snp_status = SnpStatusFlags::get_status();
    proof {
        lemma_SnpStatus_bit_valid(VTOM as _);
    }

    snp_status.contains(VTOM)
}

/// The permission to the physical address in case there are some higher
/// properties on it; e.g., if this is validated?
pub tracked struct PSnpVirtAddr {
    addr: u64,
    validated: bool,
}

impl PSnpVirtAddr {
    pub closed spec fn addr(&self) -> u64 {
        self.addr
    }

    pub closed spec fn is_validated(&self) -> bool {
        self.validated
    }

    pub proof fn validate(&mut self) {
        self.validated = true;
    }

    pub proof fn invalidate(&mut self) {
        self.validated = false;
    }
}

pub exec static SNP_VTOM: OnceCellNoPred<usize>
    ensures
        SNP_VTOM.wf(),
{
    OnceCellNoPred::new(Ghost(()))
}

pub const SEV_STATUS_MSR: u32 = 0xC0010131;

pub struct Snp;

impl Snp {
    #[inline(always)]
    #[verifier::external_body]
    fn get_page_encryption_masks(&self) -> PageEncryptionMasks {
        if has_vtom() {
            vstd::vpanic!("We do not support VTOM yet");
        } else {
            PageEncryptionMasks {
                private_pte_mask: 1 << 51,
                shared_pte_mask: 0,
                addr_mask_width: 51,
                phys_addr_sizes: 48, // todo: do not hardcode this.
            }
        }
    }
}

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }

    fn init_platform(&self, header: &Stage2LaunchInfo) {
        // Set the top of the virtual memory.
        let vtom = header.vtom as usize;
        SNP_VTOM.init(vtom);

        // Set the encryption bit.
        let masks = self.get_page_encryption_masks();
        PTE_MASK_PRIVATE.init(masks.private_pte_mask);
        PTE_MASK_SHARED.init(masks.shared_pte_mask);

        let guest_phys_addr_size = (masks.phys_addr_sizes >> 16) & 0xff;
        let host_phys_addr_size = masks.phys_addr_sizes & 0xff;
        let phys_addr_size = if guest_phys_addr_size == 0 {
            // When [GuestPhysAddrSize] is zero, refer to the PhysAddrSize field
            // for the maximum guest physical address size.
            // - APM3, E.4.7 Function 8000_0008h - Processor Capacity Parameters and Extended Feature Identification
            host_phys_addr_size
        } else {
            guest_phys_addr_size
        };

        PHYS_ADDR_SIZE.init(phys_addr_size);

        // If the C-bit is a physical address bit however, the guest physical
        // address space is effectively reduced by 1 bit.
        // - APM2, 15.34.6 Page Table Support
        let effective_phys_addr_size = if masks.addr_mask_width <= phys_addr_size {
            masks.addr_mask_width
        } else {
            phys_addr_size
        };

        assume(effective_phys_addr_size < u32::BITS);  // ugly workaround.

        let max_addr = 1 << effective_phys_addr_size;
        MAX_PHYS_ADDR.init(max_addr);

        // Initialize feature masks.
        let mut feature_mask = PteFlags::all_bits();
        // feature_mask.remove(PteFlags::GLOBAL);

        FEATURE_MASK.init(feature_mask);
    }

    // TODO: Add permission or tracked token here.
    fn validate_memory(
        &self,
        heap_start: &VirtAddr,
        heap_end: &VirtAddr,
    ) -> bool/*
        requires
            self.wf(),
            heap_start.wf(),
            heap_end.wf(),
            heap_end@ > heap_start@,
            heap_start@ % 0x1000 == 0,
            heap_end@ % 0x1000 == 0,
        */
     {
        let mut start = *heap_start;
        let end = *heap_end;

        while start.0 < end.0
            invariant
                start@ <= end@,
                self.wf(),
                heap_start.wf(),
                heap_end.wf(),
                start@ % 0x1000 == 0,
                heap_start@ % 0x1000 == 0,
                heap_end@ % 0x1000 == 0,
                heap_end@ <= LOWMEM_END as u64,
                end@ == heap_end@,
            decreases end@ - start@,
        {
            let (ret, cf) = Self::pvalidate(start.0, 0x1000, true, Tracked(()));

            start = VirtAddr(start.0 + 0x1000);
        }

        true
    }
}

impl WellFormed for Snp {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

} // verus!
deko_bitflags! {
    pub struct SnpStatus: u32 {
        const SEV = 0;
        const SEV_ES = 1;
        const SEV_SNP = 2;
        const VTOM = 3;
        const REFLECT_VS = 4;
        const REST_INJ = 5;
        const ALT_INJ = 6;
        const DBG_SWP = 7;
        const PREV_HOST_IBS = 8;
        const BTB_ISOLATION = 9;
        const VMPL_SSS = 10;
        const SECURE_TSC = 11;
        const VMSA_REG_PROT = 12;
        const SMT_PROT = 13;
    }
}

verus! {

impl SnpStatusFlags {
    /// Read the SNP status from the MSR; as this is MSR read, we mark this
    /// as `external_body`.
    #[verifier::external_body]
    #[inline(always)]
    pub fn get_status() -> (r: Self)
        ensures
            r.wf(),
    {
        let bits = read_msr(SEV_STATUS_MSR) as u32;

        SnpStatusFlags { bits, flags: Ghost(from_bits(bits)) }
    }
}

} // verus!
