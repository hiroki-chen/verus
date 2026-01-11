use deko_macros::DekoDebug;
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::cpu::write_msr;
use deko_std::prelude::{func_ptr, DekoPointsTo};
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::DekoCpuCtx;
use crate::imp::{SnpStatusFlags, GUEST_MSR_INTERCEPT, MSR_SEV_STATUS};
use crate::snp::vmsa::VMSA;
use crate::snp::SnpStatus;
use crate::{kerror, kinfo};

verus! {

/// See AMD's manual. Table B-5. INTERCEPT_MSR_VEC0 Layout
#[repr(u32)]
#[derive(DekoDebug)]
pub enum DekoMsrInterceptVec0 {
    StarRead = 8,
    StarWrite = 9,
    LstarRead = 10,
    LstarWrite = 11,
    CstarRead = 12,
    CstarWrite = 13,
}

#[derive(DekoDebug)]
pub enum DekoMsrIntercept {
    /// Intercept for MSR vector 0.
    InterceptMsrVec0(DekoMsrInterceptVec0),
}

#[verus_verify]
impl VMSA {
    /// Enable MSR intercept for the given MSR `which`.
    ///
    /// Call this function only after the vmsa page has been properly allocated
    /// and mapped on the current CPU.
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(vmsa_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(vmsa_perm).is_init(),
            old(vmsa_perm).wf(),
            old(vmsa_perm).pptr() == ptr@,
        ensures
            vmsa_perm.is_init(),
            vmsa_perm.wf(),
            vmsa_perm.pptr() == ptr@,
    )]
    pub fn enable_msr_intercept(ptr: DekoPPtr<Self>, which: DekoMsrIntercept) {
        if !check_and_enable_msr_intercept_support() {
            kerror!("SEV-SNP Guest MSR Intercept not supported on this platform");

            return ;
        }
        unsafe {
            let vmsa = ptr.addr() as *mut VMSA;

            let vec_ptrs = core::ptr::addr_of_mut!((*vmsa).intercept_msr_vecs);

            match which {
                DekoMsrIntercept::InterceptMsrVec0(vec0) => {
                    let bit = vec0 as u64;
                    let vec0_ptr = (vec_ptrs as *mut u64).add(0);
                    let mut current_val = core::ptr::read_unaligned(vec0_ptr);
                    // current_val |= 1 << bit;
                    core::ptr::write_unaligned(vec0_ptr, current_val);
                },
            }

            let sev_features_ptr = core::ptr::addr_of_mut!((*vmsa).sev_features);
            let mut sev_features = core::ptr::read_unaligned(sev_features_ptr);
            // VMSA sev_features bit is shifted by 2 as last 2 bits are ignored in the guest VMSA.
            //
            // Disable this temporarily for replacing the guest kernel when Grub is
            // complaining about invalid SEV features.
            sev_features |= (GUEST_MSR_INTERCEPT >> 2);
            core::ptr::write_unaligned(sev_features_ptr, sev_features);
        }
    }
}

/// Note that the bit `GuestinterceptCtl` may only be used if
/// "Allowed SEV Features" is enabled and the `Allowed SEV Features Mask`
/// permits the use of this feature.
pub fn check_and_enable_msr_intercept_support() -> bool {
    broadcast use SnpStatusFlags::lemma_each_bit_is_valid;

    proof {
        bit_u32_and_auto();
        bit_u64_and_auto();
    }

    // kinfo!("Checking SEV-SNP Guest MSR Intercept support...");

    // let sev_features = SnpStatusFlags::get_status();

    // kinfo!("sev_features:", sev_features);
    // if !sev_features.contains(GUEST_MSR_INTERCEPT) {
    //     // enable it.
    //     let sev_features = sev_features.bits() | GUEST_MSR_INTERCEPT;

    //     write_msr(MSR_SEV_STATUS, sev_features);
    //     kinfo!("Enabled SEV-SNP Guest MSR Intercept: ", sev_features);
    // }
    // kinfo!("SEV-SNP Guest MSR Intercept supported on this platform");

    true
}

/// The syscall hook function for guest running in the VM.
#[no_mangle]
pub fn syscall_hook() {
}

func_ptr!(syscall_hook);

/// Enable the syscall hook for guest running in the VM.
///
/// This is done by enabling the appropriate bit mask in the VMSA's intercept_msr_vec.
#[verus_spec()]
pub fn enable_syscall_hook() {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    proof_with!(Tracked(&cpu_perm) => Tracked(mut vmsa_perm));
    let vmsa = VMSA::this_vmsa(cpu);

    // Now enable the syscall hook by setting the appropriate bit in the intercept_msr_vec.
    proof_with!(Tracked(&mut vmsa_perm));
    VMSA::enable_msr_intercept(
        vmsa,
        DekoMsrIntercept::InterceptMsrVec0(DekoMsrInterceptVec0::LstarWrite),
    );
}

} // verus!
