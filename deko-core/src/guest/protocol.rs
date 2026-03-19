use deko_macros::DekoDebug;
use deko_std::address::{PhysAddr, VirtAddr};
use deko_std::wf::WellFormed;
use vstd::prelude::*;

verus! {

global layout DekoGuestLstarWriteReq is size == 0x30;

global layout DekoNewAppReq is size == 0x70;

global layout DekoMapIfcReq is size == 0x298;

#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoVmplSwitchErr {
    Ok,
    /// The VMPL switch operation was cancelled, likely due to an interrupt or other
    /// asynchronous event that occurred during the switch.
    Cancelled,
    /// The VMPL switch operation failed either because the GHCB MSR protocol didn't
    /// honor our request or some other fatal error occurred during the switch.
    Failed(u32),
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
    /// Special note on `Busy`: This indicates that the service
    /// request could not be processed at this time because
    /// the monitor is currently busy with another operation.
    /// The guest retry the request later; be sure this will
    /// not trigger a livelock.
    Busy,
    VmplSwitchErr(DekoVmplSwitchErr),
    Other(u64),
}

#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoGuestServError {
    SoftError(DekoGuestServResultCode),
    FatalError,
}

#[verus_verify]
impl DekoGuestServError {
    #[verus_spec()]
    pub fn into_result_code(&self) -> u64 {
        match self {
            DekoGuestServError::SoftError(code) => code.into_error_code(),
            DekoGuestServError::FatalError => 0xFFFF_FFFF_FFFF_FFFFu64,
        }
    }
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
            DekoGuestServResultCode::VmplSwitchErr(err) => 0x9000_0000u64,
            DekoGuestServResultCode::Other(code) => 0x8000_1000u64.wrapping_add(*code),
        }
    }
}

#[verifier::external]
impl core::fmt::Debug for DekoGuestServError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DekoGuestServError::SoftError(
                code,
            ) => write!(f, "SoftError({:?})", code.into_error_code()),
            DekoGuestServError::FatalError => write!(f, "FatalError"),
        }
    }
}

pub type DekoGuestServResult<T> = core::result::Result<T, DekoGuestServError>;

pub const DEKO_GUEST_EXIT_PROTOCOL_DEKO_SERVICE: u32 = 0x0;

pub const DEKO_GUEST_EXIT_PROTOCOL_ATTEST_SERVICE: u32 = 0x1;

pub const DEKO_GUEST_EXIT_PROTOCOL_TPM_SERVICE: u32 = 0x2;

pub const DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE: u32 = 0x4;

/// Additional data provided with a guest request.
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoGuestRequestAdditionalData {
    #[deko(hex)]
    pub guest_cr3: u64,
}

/// Parameters associated with a guest service request.
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoGuestRequestParams {
    #[deko(hex)]
    pub sev_features: u64,
    #[deko(hex)]
    pub rcx: u64,
    #[deko(hex)]
    pub rdx: u64,
    #[deko(hex)]
    pub r9: u64,
    #[deko(hex)]
    pub r8: u64,
    #[deko(hex)]
    pub additional_data: Option<DekoGuestRequestAdditionalData>,
}

pub const DEKO_SERVICE_APP_ENTER_OK: u64 = 0x9000_0000;

pub const DEKO_SERVICE_APP_EXIT: u64 = 0x9000_0001;

pub const DEKO_SERVICE_TIMER: u64 = 0x7000_0001;

pub const DEKO_SERVICE_REMAP_CA: u32 = 0x0;

pub const DEKO_SERVICE_PVALIDATE: u32 = 0x1;

pub const DEKO_SERVICE_CREATE_VCPU: u32 = 0x2;

pub const DEKO_SERVICE_DESTROY_VCPU: u32 = 0x3;

pub const DEKO_SERVICE_DEPOSIT_MEMORY: u32 = 0x4;

pub const DEKO_SERVICE_WITHDRAW_MEMORY: u32 = 0x5;

pub const DEKO_SERVICE_QUERY_PROTOCOL: u32 = 0x6;

pub const DEKO_SERVICE_ATTEST_SERVICES: u32 = 0x0;

pub const DEKO_SERVICE_ATTEST_SINGLE_SERVICE: u32 = 0x1;

pub const DEKO_SERVICE_EXTEND_MSR_INTERCEPT: u32 = 0x0;

pub const DEKO_SERVICE_EXTEND_SYSCALL_ANALYSIS: u32 = 0x1;

pub const DEKO_SERVICE_EXTEND_REPORT_APP: u32 = 0x2;

pub const DEKO_SERVICE_EXTEND_LAUNCH_APP: u32 = 0x3;

pub const DEKO_SERVICE_EXTEND_MAP_IFC: u32 = 0x4;

// Keep 0x5 aligned with Linux SVSM_EXTEND_TASK_MIGRATE.
pub const DEKO_SERVICE_EXTEND_TASK_MIGRATE: u32 = 0x5;

pub const DEKO_SERVICE_EXTEND_TIMER_EVENT: u32 = 0x6;

// VMPL1 -> VMPL0 syscall-forward request. Keep it distinct from VMPL2
// migration request (0x5) to avoid protocol collision.
pub const DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER: u32 = 0x7;

/// Represents a request structure for LSTAR MSR write operations.
/// The guest must place this request at the given physical address
/// before invoking the LSTAR write service.
#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoGuestLstarWriteReq {
    /// The guest virtual address of the syscall entry point.
    pub syscall_enter_addr: VirtAddr,
    /// The guest allocated virtual address of the trampoline area.
    pub trampoline_gva: VirtAddr,
    /// The physical address of the trampoline code.
    pub trampoline_gpa: PhysAddr,
    /// The physical address of the IFC policy engine blob.
    pub blob_gpa: PhysAddr,
    /// Guest  page offset base.
    pub page_offset_base: VirtAddr,
    /// Being returned.
    pub sysret_trampoline: u64,
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoMapIfcSingleReq {
    #[deko(hex)]
    pub va_start: u64,
    #[deko(hex)]
    pub va_end: u64,
    #[deko(hex)]
    pub pa_start: u64,
    #[deko(hex)]
    pub pa_end: u64,
    pub is_percpu: u64,
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoMapIfcReq {
    pub req_len: u16,
    pub _reserved: [u16; 3],
    pub ghcb_va: u64,
    pub db_va: u64,
    pub reqs: [DekoMapIfcSingleReq; 16],
}

#[allow(non_camel_case_types)]
#[repr(u32)]
#[derive(Copy, Clone, DekoDebug, PartialEq, Eq)]
pub enum DekoNewAppType {
    DEKO_DOCKER_INFRA = 0,
    DEKO_DOCKER_APPS = 1,
    DEKO_UNKNOWN = 0xffffffff,
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoNewAppReq {
    /// Process ID (current->pid)
    pub pid: u32,
    /// Thread Group ID (current->tgid).
    /// Used to identify the main thread.
    pub tgid: u32,
    /// Parent PID (current->real_parent->pid).
    /// Essential for building the process tree.
    pub ppid: u32,
    /// User ID (current_cred()->uid).
    /// Used for privilege checks (root vs non-root).
    pub uid: u32,
    /// Pointer or ID of the Mount Namespace.
    /// (u64)current->nsproxy->mnt_ns
    /// If two processes share this, they are in the same container filesystem view.
    pub mnt_ns_id: u64,
    /// The start code virtual address of the new application.
    pub start_code: u64,
    /// The end code virtual address of the new application.
    pub end_code: u64,
    /// The beginning of the user stack.
    pub user_stack: u64,
    /// The size of the user stack.
    pub user_stack_size: u64,
    /// Command excluding the path.
    pub comm: [u8; 16],
    /// Returned VMPL1 kernel rsp for the initial thread.
    pub kernel_vmpl1_rsp: u64,
    /// Initial FS base for the thread.
    pub fs_base: u64,
    /// Initial user GS base for the thread.
    pub gs_base: u64,
    /// Initial kernel GS base for the thread.
    pub kernel_gs_base: u64,
    pub app_type: DekoNewAppType,
}

impl WellFormed for DekoNewAppReq {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[repr(C, align(8))]
#[derive(Copy, Clone, DekoDebug)]
pub struct DekoTaskMigrateReq {
    pub old_cpu: u32,
    pub new_cpu: u32,
    pub pid: u32,
    pub _reserved: u32,
    pub kernel_gs_base: u64,
    pub user_gs_base: u64,
}

impl WellFormed for DekoTaskMigrateReq {
    open spec fn wf(&self) -> bool {
        true
    }
}

} // verus!
