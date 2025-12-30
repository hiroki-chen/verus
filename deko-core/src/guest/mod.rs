use deko_macros::DekoDebug;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

verus! {

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
    /// * `info_1` - Primary exit qualification or request ID (e.g., EXIT_INFO_1).
    /// * `info_2` - Secondary exit qualification or sub-function ID (e.g., EXIT_INFO_2).
    /// * `params` - A pointer or value representing additional parameters for the request.
    ServiceRequest { info_1: u32, info_2: u32, params: u64 },
    /// Indicates that the guest core context exists in the monitor's records
    /// but the actual vCPU has not yet been initialized or launched at the hardware level.
    ///
    /// This state may occur during the multiprocessor (AP) startup sequence where
    /// the monitor tracks the core as "live" or "pending," but the guest OS has not
    /// yet successfully executed the `VMRUN` instruction for this specific core.
    CoreNotCreated,
}

impl WellFormed for DekoGuestExitInformation {
    open spec fn wf(&self) -> bool {
        match self {
            DekoGuestExitInformation::ServiceRequest { .. } => true,
            DekoGuestExitInformation::CoreNotCreated => true,
        }
    }
}

} // verus!
