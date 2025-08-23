use core::sync::atomic::AtomicU32;

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

pub struct SEVStatusFlags;

verus! {

pub const SEV_STATUS_MSR: u32 = 0xC0010131;

// TODO: Wrap "bitflags" as a macro?
pub const SEV: u32 = 1 << 0;

pub const SEV_ES: u32 = 1 << 1;

pub const SEV_SNP: u32 = 1 << 2;

pub const VTOM: u32 = 1 << 3;

pub const REFLECT_VC: u32 = 1 << 4;

pub const REST_INJ: u32 = 1 << 5;

pub const ALT_INJ: u32 = 1 << 6;

pub const DBG_SWP: u32 = 1 << 7;

pub const PREV_HOST_IBS: u32 = 1 << 8;

pub const BTB_ISOLATION: u32 = 1 << 9;

pub const VMPL_SSS: u32 = 1 << 10;

pub const SECURE_TSC: u32 = 1 << 11;

pub const VMSA_REG_PROT: u32 = 1 << 12;

pub const SMT_PROT: u32 = 1 << 13;

pub ghost enum SnpStatus {
    Sev,
    SevEs,
    SevSnp,
    Vtom,
    ReflectVc,
    RestInj,
    AltInj,
    DbgSwp,
    PrevHostIbs,
    BtbIsolation,
    VmplSss,
    SecureTsc,
    VmsaRegProt,
    SmtProt,
}

pub struct SnpStatusFlags {
    /// Store the *actual* bits in a u32.
    bits: u32,
    /// For verification only.
    #[verifier::spec]
    flags: Ghost<Set<SnpStatus>>,
}

pub open spec fn from_bits(bits: u32) -> Set<SnpStatus> {
    Set::new(|flag: SnpStatus| flag.bit() & bits != 0)
}

impl SnpStatus {
    pub open spec fn bit(&self) -> u32 {
        match self {
            SnpStatus::Sev => SEV,
            SnpStatus::SevEs => SEV_ES,
            SnpStatus::SevSnp => SEV_SNP,
            SnpStatus::Vtom => VTOM,
            SnpStatus::ReflectVc => REFLECT_VC,
            SnpStatus::RestInj => REST_INJ,
            SnpStatus::AltInj => ALT_INJ,
            SnpStatus::DbgSwp => DBG_SWP,
            SnpStatus::PrevHostIbs => PREV_HOST_IBS,
            SnpStatus::BtbIsolation => BTB_ISOLATION,
            SnpStatus::VmplSss => VMPL_SSS,
            SnpStatus::SecureTsc => SECURE_TSC,
            SnpStatus::VmsaRegProt => VMSA_REG_PROT,
            SnpStatus::SmtProt => SMT_PROT,
        }
    }
}

impl View for SnpStatusFlags {
    type V = Set<SnpStatus>;

    closed spec fn view(&self) -> (r: Self::V) {
        self.flags@
    }
}

impl SnpStatusFlags {
    pub open spec fn inv(&self) -> bool {
        &&& forall|flag: SnpStatus| #[trigger]
            self@.contains(flag) <==> (flag.bit() & self.bits() != 0)
        &&& self@ =~= from_bits(self.bits())
    }

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

    pub closed spec fn bits(&self) -> u32 {
        self.bits
    }

    pub fn contains(&self, flag: u32) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == from_bits(flag).subset_of(self@),
    {
        let res = flag & self.bits == flag;
        proof {
            let ghost other = from_bits(flag);
            assert(other =~= Set::new(|s: SnpStatus| s.bit() & flag != 0));
            assert(self@ =~= from_bits(self.bits()));

            assert(forall|s: SnpStatus| #[trigger]
                self@.contains(s) <==> (s.bit() & self.bits() != 0));
            assert(forall|s: SnpStatus| #[trigger] other.contains(s) <==> s.bit() & flag != 0);

            // ==> Direction: If the bitwise check passes, then it's a subset.
            if res {
                assert forall|s: SnpStatus| (#[trigger] s.bit() & flag != 0) implies (s.bit()
                    & self.bits != 0) by {
                    assert(flag & self.bits == flag);
                    assert(s.bit() & flag != 0);

                    lemma_u32_subset(flag, self.bits, s.bit());
                }
            }
            if other.subset_of(self@) {
                assert(forall|s: SnpStatus| #[trigger]
                    other.contains(s) ==> s.bit() & flag != 0 && s.bit() & self.bits != 0);
                assume(flag & self.bits() == flag);
            }
        }

        res
    }

    pub fn empty() -> (r: Self)
        ensures
            r.inv(),
            r.bits() == 0,
    {
        proof {
            assert forall|flag: SnpStatus| (#[trigger] flag.bit() & 0) == 0 by {
                bit64_and_auto();
            }
            // Necessary
            assert(Set::empty() =~= from_bits(0));
        }

        SnpStatusFlags { bits: 0, flags: Ghost(Set::empty()) }
    }
}

impl WellFormed for SnpStatusFlags {
    open spec fn wf(&self) -> bool {
        self.inv()
    }
}

pub struct Snp;

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }

    fn init_platform(&self) {
        // Initialize the SNP platform.
    }
}

impl Snp {

}

} // verus!
