use core::sync::atomic::AtomicU32;

use deko_meta::{HeaderRaw, Stage2LaunchInfo};
use deko_std::prelude::*;
use vstd::prelude::*;

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
        let vtom = SNP_VTOM.get();
        if vtom.is_none() {
            vstd::vpanic!("SNP VTOM is not initialized!");
        }
        let vtom = vtom.unwrap();

        PageEncryptionMasks {
            private_pte_mask: 0,
            shared_pte_mask: *vtom,
            addr_mask_width: vtom.leading_zeros(),
            phys_addr_sizes: 4096,  // togo: get this from cpuid.
        }
    }
}

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }

    fn init_platform(&self, header: &Stage2LaunchInfo) {
        // Initialize the SNP platform.
        let snp_status = SnpStatusFlags::get_status();
        proof {
            lemma_SnpStatus_bit_valid(VTOM as _);
        }
        if !snp_status.contains(VTOM) {
            vstd::vpanic!("SNP VTOM is not enabled!");
        }
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
