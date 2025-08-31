//! The Guest-Host Communication Block (GHCB) and related functionality.
//!
//! GHCB is a protocol/data structure usde in AMD SEV-SNP to facilitate
//! communication between the guest and the hypervisor. It is used for various
//! operations, including handling certain types of exits from the guest to the
//! hypervisor.
//!
//! In this module, we define the GHCB structure and provide functions to
//! interact with it, including sending and receiving messages via the GHCB
//! protocol.
use deko_std::prelude::*;
use vstd::atomic::PAtomicU8;
use vstd::prelude::*;

verus! {

#[repr(C)]
pub struct GuestHostCommucationBlock {
    _reserved: Array<u8, 0xcb>,
    pub cpl: PAtomicU8, // tweak: this is now `repr[(C)]`
    _reserved2: Array<u8, 0x74>,
    pub xss: u64,
    _reserved3: Array<u8, 0x18>,
    pub dr7: u64,
    _reserved4: Array<u8, 0x90>,
    pub rax: u64,
    _reserved5: Array<u8, 0x100>,
    _reserved6: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbx: u64,
    _reserved7: Array<u8, 0x70>,
    /// Guest controlled exit code.
    pub sw_exitcode: u64,
    /// Guest controlled exit info 1.
    pub sw_exitinfo1: u64,
    /// Guest controlled exit info 2.
    pub sw_exitinfo2: u64,
    /// Guest controlled additional information.
    pub sw_scratch: u64,
    _reserved8: Array<u8, 0x38>,
    pub xcr0: u64,
    /// Bitmap to indicate valid qwords in the save state area
    /// starting from offset 0x000 through offset 0xe3f.
    pub valid_bitmap: Array<u8, 0x10>,
    pub x87_state_gpa: u64,
    _reserved9: Array<u8, 0x3f8>,
    pub shared_buffer: Array<u8, 0x7f0>,
    _reserved10: Array<u8, 0x0a>,
    /// Version of the GHCB protocol used by the guest.
    pub ghcb_protocol_version: u16,
    /// Provides an indicator of the usage and format of the GHCB:
    /// - 0x0000_0000: The GHCB page follows the format defined in
    ///                the AMD's manual.
    /// - Any other value can be used by the hypervisor, which can
    ///             determine its own format.
    pub ghcb_usage: u32,
}

impl WellFormed for GuestHostCommucationBlock {
    closed spec fn wf(&self) -> bool {
        &&& self.ghcb_protocol_version == 0x0001 || self.ghcb_protocol_version == 0x0002
        &&& self.ghcb_usage == 0x0000_0000
    }
}

/// Fetch the current GHCB structure for this specific CPU core.
#[verifier::external_body]
fn current_ghcb() -> &'static GuestHostCommucationBlock {
  vstd::vpanic!("todo")
}

} // verus!
