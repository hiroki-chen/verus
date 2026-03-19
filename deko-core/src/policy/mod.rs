use deko_macros::DekoDebug;
use deko_std::address::VirtAddr;
use deko_std::wf::WellFormed;
use deko_std::with_permission;
use vstd::prelude::*;

use crate::policy::userapp::setup_vmpl1_func_ptr;

pub(crate) mod fs;
pub(crate) mod ifc;
pub(crate) mod intercept;
pub(crate) mod labels;
pub(crate) mod msr;
pub(crate) mod syscall;
pub(crate) mod userapp;

pub use intercept::{
    enable_syscall_hook, DekoIntercept, DekoInterceptVec, DekoInterceptVec0, DekoInterceptVec2,
    DekoInterceptVec3, DekoInterceptVec4, DekoMsrIntercept, DekoMsrInterceptVec0,
};

pub use crate::mm::paging::RECURSIVE_INDEX;

verus! {

global layout DekoSyscallBody is size == 0x50;

/// The policy engine is responsible for enforcing security policies.
#[derive(DekoDebug)]
pub struct DekoPolicyEngine {}

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
