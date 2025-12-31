use deko_macros::DekoDebug;
use deko_std::deko_rwlock_read_atomic_data;
use deko_std::prelude::DekoPointsTo;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtx, PERCPU_AREAS};
use crate::imp::vmsa::{GuestVMExit, VMSA};
use crate::{kerror, kwarn};

verus! {

#[derive(DekoDebug)]
pub struct DekoGuestRequestParams {
    pub sev_features: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub r8: u64,
}

// impl DekoGuestRequestParams {
//     #[verus_spec(
//         with
//             Tracked(vmsa_perm): Tracked<DekoPointsTo<VMSA>>,
//         requires
//             vmsa_perm.wf(),
//             vmsa_perm.is_init(),
//             vmsa_perm.pptr() == vmsa,
//     )]
//     pub fn try_parse_vmsa(vmsa: DekoPPtr<VMSA>) -> Self {
//         let vmsa = vmsa.borrow(Tracked(&vmsa_perm));
//         Self {
//         }
//     }
// }
/// Represents the reason for a guest VM exit event intercepted by the VMPL0 monitor.
///
/// This enum captures the state and intent of a guest vCPU when it exits execution
/// and control is transferred to the secure monitor (Deko). It distinguishes between
/// active service requests and state synchronization issues during core initialization.
#[derive(DekoDebug)]
pub enum DekoGuestExitInformation {
    /// Indicates that the guest core requested a service from the hypervisor
    /// which was intercepted (trapped) by VMPL0.
    ///
    /// This typically corresponds to a `#VMEXIT` caused by a specific instruction
    /// (like `VMMCALL` or `CPUID`) that the monitor must inspect or emulate
    /// before potentially forwarding it to the host hypervisor.
    ///
    /// # Fields
    /// * `protocol` - The service protocol identifier requested by the guest.
    /// * `req` - The specific service request code within the protocol.
    /// * `params` - Parameters associated with the service request, encapsulated
    ///             in a [`DekoGuestRequestParams`] struct.
    ServiceRequest { protocol: u32, req: u32, params: DekoGuestRequestParams },
    /// Indicates that the guest core context exists in the monitor's records
    /// but the actual vCPU has not yet been initialized or launched at the hardware level.
    ///
    /// This state may occur during the multiprocessor (AP) startup sequence where
    /// the monitor tracks the core as "live" or "pending," but the guest OS has not
    /// yet successfully executed the `VMRUN` instruction for this specific core.
    CoreNotCreated,
    /// Indicates that the VMPL switch operation failed.
    VmplSwitchFailed,
}

impl WellFormed for DekoGuestExitInformation {
    open spec fn wf(&self) -> bool {
        match self {
            DekoGuestExitInformation::ServiceRequest { .. } => true,
            DekoGuestExitInformation::CoreNotCreated => true,
            DekoGuestExitInformation::VmplSwitchFailed => true,
        }
    }
}

#[verus_verify]
impl DekoGuestExitInformation {
    #[verus_spec(
        with
            Tracked(vmsa_perm): Tracked<&DekoPointsTo<VMSA>>,
        requires
            vmsa_perm.wf(),
            vmsa_perm.is_init(),
            vmsa_perm.pptr() == vmsa@,
    )]
    fn try_parse_vmsa(vmsa: DekoPPtr<VMSA>) -> Option<Self> {
        let vmsa = vmsa.borrow(Tracked(vmsa_perm));
        let exit_code = vmsa.guest_exit_code.0;

        if exit_code != 0x403  /* VMGEXIT */
         {
            let protocol = (vmsa.rax >> 32) as u32;
            let req = (vmsa.rax & 0xFFFFFFFFu64) as u32;
            let params = DekoGuestRequestParams {
                sev_features: vmsa.sev_features,
                rcx: vmsa.rcx,
                rdx: vmsa.rdx,
                r8: vmsa.r8,
            };

            Some(DekoGuestExitInformation::ServiceRequest { protocol, req, params })
        } else {
            kerror!("Unsupported guest exit code: ", exit_code);

            None
        }

    }

    #[verus_spec()]
    pub fn get_guest_exit_information() -> Option<Self> {
        let (this_cpu, Tracked(this_cpu_perm)) = DekoCpuCtx::this_cpu();
        let cpu_index = this_cpu.borrow(Tracked(&this_cpu_perm.ptr_perm)).cpu_id;

        let (caa) =
            deko_rwlock_read_atomic_data! {
            PERCPU_AREAS,
            percpu_areas,
            percpu_areas_perm,
            {
                crate::check_shared_cpu_idx!(cpu_index as usize, percpu_areas, percpu_areas);

                let vmsa = &percpu_areas.0[cpu_index as usize].guest_vmsa;

                deko_rwlock_read_atomic_data! {
                    vmsa,
                    vmsa,
                    vmsa_perm,
                    {
                        vmsa.caa
                    }
                }
            }
        };

        match caa {
            Some(caa) => {
                proof_with!(Tracked(&this_cpu_perm) => Tracked(vmsa_perm));
                let vmsa = VMSA::this_vmsa(this_cpu);

                proof_with!(Tracked(&vmsa_perm));
                Self::try_parse_vmsa(vmsa)
            },
            None => {
                kwarn!("Guest caa not created for CPU index ", cpu_index);
                None
            },
        }
    }
}

} // verus!
