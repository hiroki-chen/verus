use deko_macros::DekoDebug;
use deko_std::address::VirtAddr;
use deko_std::wf::WellFormed;
use deko_std::with_permission;
use vstd::prelude::*;

use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
use crate::policy::userapp::setup_vmpl1_func_ptr;

pub(crate) mod config;
pub(crate) mod fs;
pub(crate) mod ifc;
pub(crate) mod intercept;
pub(crate) mod lattice;
pub(crate) mod mapping;
pub(crate) mod msr;
pub(crate) mod syscall;
pub(crate) mod userapp;

#[cfg(feature = "alloc")]
pub use config::PolicyConfigToml;
pub use intercept::{
    enable_syscall_hook, DekoIntercept, DekoInterceptVec, DekoInterceptVec0, DekoInterceptVec2,
    DekoInterceptVec3, DekoInterceptVec4, DekoMsrIntercept, DekoMsrInterceptVec0,
};

pub use crate::mm::paging::RECURSIVE_INDEX;

verus! {

global layout DekoSyscallBody is size == 0x50;

/// The policy engine is responsible for enforcing security policies.
#[derive(DekoDebug)]
pub struct DekoPolicyEngine {
    #[cfg(feature = "alloc")]
    #[deko(skip)]
    lattice: lattice::FiniteLattice,
}

#[verus_verify]
impl DekoPolicyEngine {
    #[cfg(feature = "alloc")]
    pub closed spec fn wf(&self) -> bool {
        self.lattice.wf()
    }

    /// Initializes the policy engine from a byte buffer that contains the TOML
    /// configuration for the policies.
    #[cfg(feature = "alloc")]
    #[verus_spec(r =>
        ensures
            r matches Ok(engine) ==> engine.wf(),
    )]
    pub fn init_from_bytes(buf: &[u8]) -> DekoGuestServResult<Self> {
        let policy = config::parse_policy_config_from_bytes(buf)?;
        let lattice = lattice::FiniteLattice::compile(&policy.lattice).map_err(
            |_err| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidFormat),
        )?;
        Ok(DekoPolicyEngine { lattice })
    }
}

/// A policy domain represents a security boundary within which certain
/// policies are enforced.
///
/// You can think of a policy domain as a sandboxed environment where
/// specific security rules and restrictions apply to the code and data
/// operating within that domain.
#[derive(DekoDebug)]
pub struct DekoPolicyDomain {}

with_permission!(
    DekoPolicyDomain,
);

#[repr(C, align(8))]
#[derive(DekoDebug, Clone, Copy)]
pub struct DekoSyscallBody {
    #[deko(hex)]
    pub rax: u64,  // Syscall number
    #[deko(hex)]
    pub rdi: u64,  // Arg 1
    #[deko(hex)]
    pub rsi: u64,  // Arg 2
    #[deko(hex)]
    pub rdx: u64,  // Arg 3
    #[deko(hex)]
    pub r10: u64,  // Arg 4
    #[deko(hex)]
    pub r8: u64,  // Arg 5
    #[deko(hex)]
    pub r9: u64,  // Arg 6
    #[deko(hex)]
    pub rcx: u64,  // Return Address
    #[deko(hex)]
    pub r11: u64,  // RFLAG
    // The current cr3.
    #[deko(hex)]
    pub cr3: u64,
}

impl WellFormed for DekoSyscallBody {
    open spec fn wf(&self) -> bool {
        true
    }
}

} // verus!
