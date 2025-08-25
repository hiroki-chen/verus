use core::sync::atomic::AtomicU32;

use deko_meta::{HeaderRaw, Stage2LaunchInfo};
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::msr::read_msr;
use crate::hal::{PlatformApi, PlatformType};

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

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }

    fn init_platform(&self, header: &Stage2LaunchInfo) {
        // Initialize the SNP platform.
        let snp_status = SnpStatusFlags::get_status();
        if !snp_status.contains(VTOM) {
            vstd::vpanic!("SNP VTOM is not enabled!");
        }
        // Set the top of the virtual memory.

        let vtom = header.vtom as usize;
        SNP_VTOM.init(vtom);
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
}
