use deko_macros::DekoDebug;
use deko_std::address::PhysAddr;
use deko_std::mem::PERCPU_CAA_BASE;
use deko_std::prelude::DekoPointsTo;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use deko_std::{deko_rwlock_read_atomic_data, trace_is_enabled};
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use crate::guest::service::handle_guest_exit_deko_service;
use crate::imp::vmsa::{GuestVMExit, VMSA};
use crate::{kerror, kinfo, kwarn};

pub(crate) mod service;

verus! {

#[repr(C, packed)]
#[derive(DekoDebug, Clone, Copy)]
pub struct CaaArea {
    pub call_pending: u8,
    pub mem_available: u8,
    pub no_eoi_required: u8,
    #[deko(skip)]
    pub reserved: [u8; 5],
}

impl WellFormed for CaaArea {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[verus_verify]
impl CaaArea {
    /// Try to fetch the caa page from the current CPU.
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(cpu_perm): Tracked<&DekoCpuCtxPermission>,
                -> caa_perm: Tracked<DekoPointsTo<CaaArea>>,
        requires
            cpu_perm.wf_with(ptr),
        ensures
            r@ == caa_perm@.pptr(),
            caa_perm@.is_init(),
            caa_perm@.wf(),
    )]
    pub fn this_caa(ptr: DekoPPtr<DekoCpuCtx>) -> DekoPPtr<Self> {
        proof_with!(|= Tracked::assume_new());
        DekoPPtr(vstd::simple_pptr::PPtr(PERCPU_CAA_BASE.0 as usize, core::marker::PhantomData))
    }
}

#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoGuestServResultCode {
    Success,
    Incomplete,
    UnsupportedProtocol,
    UnsupportedCall,
    InvalidAddr,
    InvalidFormat,
    InvalidParam,
    InvalidReq,
    Busy,
    Other(u64),
}

#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoGuestServError {
    SoftError(DekoGuestServResultCode),
    FatalError,
}

#[verus_verify]
impl DekoGuestServResultCode {
    #[verus_spec()]
    pub fn into_error_code(&self) -> u64 {
        match self {
            DekoGuestServResultCode::Success => 0,
            DekoGuestServResultCode::Incomplete => 0x8000_0000,
            DekoGuestServResultCode::UnsupportedProtocol => 0x8000_0001,
            DekoGuestServResultCode::UnsupportedCall => 0x8000_0002,
            DekoGuestServResultCode::InvalidAddr => 0x8000_0003,
            DekoGuestServResultCode::InvalidFormat => 0x8000_0004,
            DekoGuestServResultCode::InvalidParam => 0x8000_0005,
            DekoGuestServResultCode::InvalidReq => 0x8000_0006,
            DekoGuestServResultCode::Busy => 0x8000_0007,
            DekoGuestServResultCode::Other(code) => 0x8000_1000u64.wrapping_add(*code),
        }
    }
}

pub type DekoGuestServResult<T> = core::result::Result<T, DekoGuestServError>;

pub const DEKO_GUEST_EXIT_PROTOCOL_DEKO_SERVICE: u32 = 0x0;

pub const DEKO_GUEST_EXIT_PROTOCOL_ATTEST_SERVICE: u32 = 0x1;

#[derive(DekoDebug)]
pub struct DekoGuestRequestParams {
    #[deko(hex)]
    pub sev_features: u64,
    #[deko(hex)]
    pub rcx: u64,
    #[deko(hex)]
    pub rdx: u64,
    #[deko(hex)]
    pub r8: u64,
}

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

        if exit_code == 0x403  /* VMGEXIT */
         {
            let protocol = (vmsa.rax >> 32) as u32;
            let req = (vmsa.rax & 0xFFFFFFFFu64) as u32;
            // FIXME: Perhaps there are some packed <-> unpacked issues here.
            // the bit orders seem reversed.
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

                proof_with!(Tracked(&this_cpu_perm) => Tracked(mut caa_perm));
                let caa = CaaArea::this_caa(this_cpu);

                let v = caa.take(Tracked(&mut caa_perm));

                if v.call_pending != 1 {
                    // No call pending.
                    return None;
                }
                caa.write(
                    Tracked(&mut caa_perm),
                    CaaArea {
                        call_pending: 0,  // clear it.
                        mem_available: v.mem_available,
                        no_eoi_required: v.no_eoi_required,
                        reserved: v.reserved,
                    },
                );

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

/// Handle a guest exit request based on the provided protocol, request code,
/// and associated parameters.
#[verus_spec(r =>
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf(),
    ensures
        cpu_perm.wf(),
)]
pub fn handle_guest_exit(
    protocol: u32,
    req: u32,
    params: &mut DekoGuestRequestParams,
) -> DekoGuestServResult<()> {
    match protocol {
        DEKO_GUEST_EXIT_PROTOCOL_DEKO_SERVICE => {
            proof_with!(Tracked(cpu_perm));
            service::handle_guest_exit_deko_service(req, params)
        },
        _ => {
            kerror!("Unsupported guest exit protocol: ", protocol);
            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
}

} // verus!
