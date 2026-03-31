use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VirtAddr};
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M, PERCPU_CAA_BASE};
use deko_std::prelude::{DekoPointsTo, VADDR_UPPER_MASK};
use deko_std::ptr::DekoPPtr;
use deko_std::sync::DekoSimpleOnceCell;
use deko_std::wf::WellFormed;
use deko_std::{
    deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data, trace_is_enabled, TrivialPredicate,
};
use vstd::prelude::*;

use crate::cpu::irq::log_nested_irq_state;
use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission, PERCPU_AREAS};
use crate::imp::ghcb::vmpl_switch_with_rax;
use crate::imp::vmsa::{GuestVMExit, VMSA};
use crate::imp::VMPL_GUEST_DEKO_MONITOR;
use crate::mm::check_within_guest_mmap;
use crate::mm::paging::{PageTable, PageTablePermission};
use crate::mm::vm::TempMapping;
use crate::policy::DekoSyscallBody;
use crate::snp::{doorbell, is_vmpl1, is_vmpl1_kernel, is_vmpl1_user};
use crate::{kdebug, kerror, kinfo, kwarn};

pub(crate) mod hook;
pub(crate) mod paging;
pub mod protocol;
pub(crate) mod service;
pub(crate) mod service_extend;
pub(crate) mod service_memory;
pub(crate) mod service_vcpu;
pub(crate) mod userapp_runtime;

pub use hook::{install_hook, GUEST_TRAMPOLINE_MAGIC, GUEST_TRAMPOLINE_PML4_HOLE};
pub use paging::{guest_phys_to_virt, GuestMapping, GuestPageOffsetBase, GUEST_PAGE_OFFSET_BASE};
pub use protocol::{
    DekoGuestRequestAdditionalData, DekoGuestRequestParams, DekoGuestServError,
    DekoGuestServResult, DekoGuestServResultCode, DekoGuestTrampolineSetupReq, DekoLoadPolicyReq,
    DekoMapIfcReq, DekoMapIfcSingleReq, DekoNewAppReq, DekoNewAppType, DekoTaskMigrateReq,
    DekoVmplSwitchErr, DEKO_GUEST_EXIT_PROTOCOL_ATTEST_SERVICE,
    DEKO_GUEST_EXIT_PROTOCOL_DEKO_SERVICE, DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE,
    DEKO_GUEST_EXIT_PROTOCOL_TPM_SERVICE, DEKO_SERVICE_APP_ENTER_OK, DEKO_SERVICE_APP_EXIT,
    DEKO_SERVICE_ATTEST_SERVICES, DEKO_SERVICE_ATTEST_SINGLE_SERVICE, DEKO_SERVICE_CREATE_VCPU,
    DEKO_SERVICE_DEPOSIT_MEMORY, DEKO_SERVICE_DESTROY_VCPU,
    DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER, DEKO_SERVICE_EXTEND_LAUNCH_APP,
    DEKO_SERVICE_EXTEND_LOAD_POLICY, DEKO_SERVICE_EXTEND_MAP_IFC, DEKO_SERVICE_EXTEND_REPORT_APP,
    DEKO_SERVICE_EXTEND_SYSCALL_ANALYSIS, DEKO_SERVICE_EXTEND_TASK_MIGRATE,
    DEKO_SERVICE_EXTEND_TIMER_EVENT, DEKO_SERVICE_EXTEND_TRAMPOLINE_SETUP, DEKO_SERVICE_PVALIDATE,
    DEKO_SERVICE_QUERY_PROTOCOL, DEKO_SERVICE_REMAP_CA, DEKO_SERVICE_TIMER,
    DEKO_SERVICE_WITHDRAW_MEMORY,
};
pub(crate) use userapp_runtime::{
    bind_current_cpu_vmpl1_slot, copy_from_user, stage_fake_vmpl1_handoff_request,
};

verus! {

pub open spec fn valid_guest_page_addr_spec(pa: u64) -> bool {
    &&& pa % PAGE_SIZE == 0
    &&& pa < 0x000f_ffff_ffff_f000u64 - PAGE_SIZE
}

#[inline]
#[verus_spec(r =>
    ensures
        r == valid_guest_page_addr_spec(pa),
)]
pub fn valid_guest_page_addr(pa: u64) -> bool {
    pa % PAGE_SIZE == 0 && pa < 0x000f_ffff_ffff_f000u64 - PAGE_SIZE
}

#[inline]
#[verus_spec(r =>
    requires
        pa.wf(),
    ensures
        r ==> valid_guest_page_addr_spec(pa.0),
)]
pub fn valid_guest_page(pa: PhysAddr) -> bool {
    valid_guest_page_addr(pa.0) && check_within_guest_mmap(pa)
}

pub open spec fn valid_trampoline_gpa_spec(pa: u64) -> bool {
    &&& pa % PAGE_SIZE == 0
    &&& pa < 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M
}

#[inline]
#[verus_spec(r =>
    ensures
        r == valid_trampoline_gpa_spec(pa),
)]
pub fn valid_trampoline_gpa(pa: u64) -> bool {
    pa % PAGE_SIZE == 0 && pa < 0x0000_FFFF_FFFF_F000u64 - PAGE_SIZE_2M
}

pub open spec fn valid_kernel_vaddr_spec(va: u64) -> bool {
    va >= VADDR_UPPER_MASK
}

#[inline]
#[verus_spec(r =>
    ensures
        r == valid_kernel_vaddr_spec(va.0),
)]
pub fn valid_kernel_vaddr(va: VirtAddr) -> bool {
    va.0 >= VADDR_UPPER_MASK
}

global layout PtRegs is size == 0xa8, align == 8;

/// Linux `pt_regs` structure representing the CPU registers
/// saved during a context switch or interrupt.
#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct PtRegs {
    /*
     * C ABI says these regs are callee-preserved. They aren't saved on
     * kernel entry unless syscall needs a complete, fully filled
     * "struct pt_regs".
     */
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub bp: u64,
    pub bx: u64,
    /* These regs are callee-clobbered. Always saved on kernel entry. */
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub ax: u64,
    pub cx: u64,
    pub dx: u64,
    pub si: u64,
    pub di: u64,
    /*
     * orig_ax is used on entry for:
     * - the syscall number (syscall, sysenter, int80)
     * - error_code stored by the CPU on traps and exceptions
     * - the interrupt number for device interrupts
     *
     * A FRED stack frame starts here:
     *   1) It _always_ includes an error code;
     *
     *   2) The return frame for ERET[US] starts here, but
     *      the content of orig_ax is ignored.
     */
    pub orig_ax: u64,
    /* The IRETQ return frame starts here */
    pub ip: u64,
    pub cs: u64,
    pub flags: u64,
    pub sp: u64,
    pub ss: u64,
}

impl WellFormed for PtRegs {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl PtRegs {
    /// Checks whether this [`PtRegs`] instance represents the user-space register state.
    pub open spec fn is_user_regs(&self) -> bool {
        true
    }
}

/// Represents the reason for a guest VM exit event when forwarded to the monitor.
#[repr(u64)]
#[allow(non_snake_case)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoGuestExitReason {
    /// Caused by an external interrupt while the guest was running.
    INTR = 0x60,
    /// Caused by a virtual interrupt-window exit.
    VINTR = 0x64,
    /// We need to intercept the VMMCALL instruction from the guest.
    VMMCALL = 0x81,
    /// Caused by an explicit VMGEXIT via GHCB instruction
    /// and the protocol is a SVSM call.
    VMGEXIT = 0x403,
}

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
            DekoGuestExitInformation::ServiceRequest { protocol, req, params } => match *protocol {
                DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE => params.additional_data is Some,
                _ => true,
            },
            DekoGuestExitInformation::CoreNotCreated => true,
            DekoGuestExitInformation::VmplSwitchFailed => true,
        }
    }
}

#[verus_verify]
impl DekoGuestExitInformation {
    #[inline(always)]
    /// Asynchronous interrupt exits are not guest-issued protocol requests.
    /// The request parser should treat them as re-entry noise.
    pub fn is_spurious_exit_code(exit_code: u64) -> bool {
        exit_code == DekoGuestExitReason::INTR as u64 || exit_code
            == DekoGuestExitReason::VINTR as u64
    }

    #[verus_spec(r =>
        with
            Tracked(vmsa_perm): Tracked<&DekoPointsTo<VMSA>>,
        requires
            vmsa_perm.wf(),
            vmsa_perm.is_init(),
            vmsa_perm.pptr() == vmsa@,
        ensures
            r.wf(),
    )]
    pub fn try_parse_vmsa(vmsa: DekoPPtr<VMSA>, call_pending: bool) -> Option<Self> {
        let vmsa = vmsa.borrow(Tracked(vmsa_perm));
        let exit_code = vmsa.guest_exit_code.0;

        if exit_code == DekoGuestExitReason::VMGEXIT as u64 {
            let protocol = (vmsa.rax >> 32) as u32;
            let req = (vmsa.rax & 0xFFFFFFFFu64) as u32;

            // Only treat a VMGEXIT as a real service request if the caller
            // had explicitly marked a call as pending. Otherwise this is
            // noise from an async/accidental exit and should be ignored.
            if !call_pending {
                return None;
            }
            let ai = if protocol == DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE {
                Some(DekoGuestRequestAdditionalData { guest_cr3: vmsa.cr3 })
            } else {
                None
            };

            let params = DekoGuestRequestParams {
                sev_features: vmsa.sev_features,
                rcx: vmsa.rcx,
                rdx: vmsa.rdx,
                r9: vmsa.r9,
                r8: vmsa.r8,
                additional_data: ai,
            };

            Some(DekoGuestExitInformation::ServiceRequest { protocol, req, params })
        } else if Self::is_spurious_exit_code(exit_code) {
            // Leave async interrupt exits to the outer guest-entry loop.
            // They do not consume a staged guest request.
            None
        } else {
            kerror!("Unsupported guest exit code: ", exit_code=>hex);
            kerror!("Dumping VMSA: ", vmsa);

            None
        }

    }

    #[verus_spec(r =>
        ensures
            r.wf(),
    )]
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
                let call_pending = v.call_pending;

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
                let info = Self::try_parse_vmsa(vmsa, call_pending != 0);

                if info.is_none() && call_pending != 0 && !Self::is_spurious_exit_code(
                    vmsa.borrow(Tracked(&vmsa_perm)).guest_exit_code.0,
                ) {
                    // We clear call_pending before decoding the exit. Restore
                    // it for unknown non-spurious exits so the guest request
                    // is retried instead of being dropped.
                    let v = caa.take(Tracked(&mut caa_perm));
                    caa.write(
                        Tracked(&mut caa_perm),
                        CaaArea {
                            call_pending: 1,
                            mem_available: v.mem_available,
                            no_eoi_required: v.no_eoi_required,
                            reserved: v.reserved,
                        },
                    );
                }
                info
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
        old(cpu_perm).ptr_perm.value().cpu_id == cpu_idx,
        protocol == DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE ==> old(params).additional_data is Some,
    ensures
        cpu_perm.wf(),
        cpu_perm.ptr_perm.value().cpu_id == cpu_idx,
)]
pub fn handle_guest_exit(
    protocol: u32,
    req: u32,
    params: &mut DekoGuestRequestParams,
    cpu_idx: u64,
) -> DekoGuestServResult<u64> {
    kdebug!("Handling guest exit request: protocol=", protocol, ", req=", req, ", cpu_idx=", cpu_idx);

    match protocol {
        DEKO_GUEST_EXIT_PROTOCOL_DEKO_SERVICE => {
            proof_with!(Tracked(cpu_perm));
            service::handle_guest_exit_deko_service(req, params, cpu_idx)?;
            Ok(0)
        },
        DEKO_GUEST_EXIT_PROTOCOL_ATTEST_SERVICE => {
            proof_with!(Tracked(cpu_perm));
            service::handle_guest_exit_attest_service(req, params, cpu_idx)?;
            Ok(0)
        },
        DEKO_GUEST_EXIT_PROTOCOL_TPM_SERVICE => {
            // NO vTPM now.
            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
        DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE => {
            proof_with!(Tracked(cpu_perm));
            service_extend::handle_guest_exit_extend_service(req, params, cpu_idx)
        },
        _ => {
            // Sometimes this will get hit by APIC setup of the
            // guest kernel. However, returning error to the
            // function confuses the kernel and will trigger
            // a #PF when booting the guest.
            kerror!("Unsupported guest exit protocol: ");
            kerror!(" protocol=", protocol);
            kerror!(" req=", req);
            kerror!(" params=", params);

            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::UnsupportedProtocol))
        },
    }
}

/// Temporarily maps the guest's page table into the monitor's address space
/// so that we can walk the guest page tables.
#[inline]
#[verus_spec(r =>
    ensures
        r matches Ok(tm) ==> {
            &&& tm.wf()
            &&& tm.inner.end@ - tm.inner.start@ == PAGE_SIZE
        }
)]
pub fn guest_page_table(cr3: u64) -> DekoGuestServResult<TempMapping> {
    if core::hint::unlikely(!valid_guest_page_addr(cr3)) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    Ok(
        TempMapping::new(create_paddr_range(PhysAddr(cr3), 1)).ok_or(
            DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidAddr),
        )?,
    )
}

/// Used by the VMPL1 guest to request a service of the VMPL0 monitor.
#[verifier::external_body]
pub fn request_vmpl2_syscall_handler() -> DekoGuestServResult<()> {
    let extend_service = ((DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE as u64) << 32)
        | DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER as u64;

    set_vmpl1_call_pending(true);
    match vmpl_switch_with_rax(VMPL_GUEST_DEKO_MONITOR, extend_service) {
        DekoVmplSwitchErr::Ok => { return Ok(()) },
        e => {
            set_vmpl1_call_pending(false);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::VmplSwitchErr(e)));
        },
    }
}

/// Used by the VMPL1 guest to notify VMPL0 monitor of a timer event.
#[verifier::external_body]
pub fn request_vmpl2_timer_event() -> DekoGuestServResult<()> {
    let extend_service = ((DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE as u64) << 32)
        | DEKO_SERVICE_EXTEND_TIMER_EVENT as u64;

    set_vmpl1_call_pending(true);

    match vmpl_switch_with_rax(VMPL_GUEST_DEKO_MONITOR, extend_service) {
        DekoVmplSwitchErr::Ok => { return Ok(()) },
        e => {
            set_vmpl1_call_pending(false);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::VmplSwitchErr(e)));
        },
    }
}

#[verifier::external_body]
pub fn set_vmpl1_call_pending(call_pending: bool) {
    if !is_vmpl1() {
        return ;
    }
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        return ;
    };
    deko_rwlock_write_atomic_data! {
        ext_vmpl1.call_pending,
        pending,
        __,
        {
            pending = call_pending;
        }
    };
}

#[verifier::external_body]
pub fn take_vmpl1_call_pending() -> bool {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        return false;
    };
    deko_rwlock_write_atomic_data! {
        ext_vmpl1.call_pending,
        pending,
        __,
        {
            let was_pending = pending;
            pending = false;
            was_pending
        }
    }
}

#[verifier::external_body]
pub fn take_vmpl1_deferred_timer_event() -> bool {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        return false;
    };
    deko_rwlock_write_atomic_data! {
        ext_vmpl1.deferred_timer_event,
        pending,
        __,
        {
            let was_pending = pending;
            pending = false;
            was_pending
        }
    }
}

} // verus!
