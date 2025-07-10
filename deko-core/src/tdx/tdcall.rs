//! This crate implements the TDX (Trusted Domain eXtension) call interface for the Deko monitor
//!
//! This crate only implements TDCALLs necessary for the TDP spec. Other conventional TDX calls
//! will be forwarded to the untrusted hypervisor to communicate with the TDX module.
use vstd::prelude::*;

use super::Tdx;

core::arch::global_asm!(include_str!("tdcall.S"), options(att_syntax));

extern "C" {
    #[link_name = "_td_call"]
    pub fn td_call_asm(args: *mut TdcallArgs) -> u64;
}

verus! {

/// TDCALL error codes.
///
/// The higher 32 bits of the rax indicate the error code.
pub enum TdCallError {
    /// There is no valid #VE information.
    TdxNoValidVeInfo,
    /// Operand is invalid.
    TdxOperandInvalid,
    /// The operand is busy (e.g., it is locked in Exclusive mode).
    TdxOperandBusy,
    /// Page has already been accepted.
    TdxPageAlreadyAccepted,
    /// Requested page size does not match the current GPA mapping size.
    TdxPageSizeMismatch,
    /// The provided FIELD_ID is incorrect.
    TdxMetadataFieldIdIncorrect,
    /// Field code and write mask are for a read-only field.
    TdxMetadataFieldNotWritable,
    /// Field code is for an unreadable field.
    TdxMetadataFieldNotReadable,
    /// The provided field value is not valid.
    TdxMetadataFieldValueNotValid,
    /// The TD's OP_STATE is incorrect for the required operation.
    TdxOpStateIncorrect,
    /// Operand address is out of range (e.g., not in a TDMR).
    TdxOperandAddrRangeError,
    /// Physical page metadata (in PAMT) are incorrect for the requested operation.
    TdxPageMetadataIncorrect,
    /// Service TD hash of TDINFO_STRUCT does not match the currently bound hash.
    TdxServtdInfoHashMismatch,
    /// Service TD is not bound.
    TdxServtdNotBound,
    /// Service TD UUID does not match the currently bound UUID.
    TdxServtdUuidMismatch,
    /// Target TD UUID does not match the requested TD_UUID.
    TdxTargetUuidMismatch,
    /// Target TD UUID does not match the requested TD_UUID, but pre-migration target TD UUID does match it.
    TdxTargetUuidUpdated,
    /// TD is in a FATAL error state.
    TdxTdFatal,
    /// TD keys have not been configured on the hardware.
    TdxTdKeysNotConfigured,
    /// TDCS pages have not been allocated.
    TdxTdcsNotAllocated,
    Other,
}

#[repr(u64)]
pub enum TdcallNum {
    VpInfo = 1,
    MrRtmrExtend = 2,
    VpVeinfoGet = 3,
    MrReport = 4,
    VpCpuidveSet = 5,
    MemPageAccept = 6,
    VmRd = 7,
    VmWr = 8,
    ServetdRd = 18,
    ServetdWr = 20,
    MrVerifyreport = 22,
    MemPageAttrRd = 23,
    MemPageAttrWr = 24,
    VpEnter = 25,
    VpInvept = 26,
    VpInvgla = 27,
}

#[repr(C, align(8))]
pub struct TdcallArgs {
    pub rax: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
}

impl Default for TdcallArgs {
    fn default() -> (result: Self)
        ensures
            result.rax == 0 && result.rcx == 0 && result.rdx == 0 && result.r8 == 0 && result.r9
                == 0 && result.r10 == 0 && result.r11 == 0 && result.r12 == 0 && result.r13 == 0,
    {
        TdcallArgs { rax: 0, rcx: 0, rdx: 0, r8: 0, r9: 0, r10: 0, r11: 0, r12: 0, r13: 0 }
    }
}

impl From<u64> for TdCallError {
    fn from(code: u64) -> Self {
        // Convert the error code to the TdCallError enum.
        // This is a placeholder as we don't have specific error codes defined yet.
        match code {
            0x0000_0B0A => Self::TdxPageAlreadyAccepted,
            0x8000_0200 => Self::TdxOperandBusy,
            0x8000_0810 => Self::TdxTdKeysNotConfigured,
            0xC000_0100 => Self::TdxOperandInvalid,
            0xC000_0101 => Self::TdxOperandAddrRangeError,
            0xC000_0300 => Self::TdxPageMetadataIncorrect,
            0xC000_0606 => Self::TdxTdcsNotAllocated,
            0xC000_0608 => Self::TdxOpStateIncorrect,
            0xC000_0704 => Self::TdxNoValidVeInfo,
            0xC000_0B0B => Self::TdxPageSizeMismatch,
            0xC000_0C00 => Self::TdxMetadataFieldIdIncorrect,
            0xC000_0C01 => Self::TdxMetadataFieldNotWritable,
            0xC000_0C02 => Self::TdxMetadataFieldNotReadable,
            0xC000_0C03 => Self::TdxMetadataFieldValueNotValid,
            0xC000_0D03 => Self::TdxServtdInfoHashMismatch,
            0xC000_0D04 => Self::TdxServtdUuidMismatch,
            0xC000_0D05 => Self::TdxServtdNotBound,
            0xC000_0D07 => Self::TdxTargetUuidMismatch,
            0xC000_0D08 => Self::TdxTargetUuidUpdated,
            0xE000_0604 => Self::TdxTdFatal,
            _ => Self::Other,  // Default case for now
        }
    }
}

impl Tdx {
    /// Wrapper for the TDX call interface.
    ///
    /// Unfortunately we cannot verify the correctness of the assembly code so we
    /// assume it's implemeneted in the correct way and we only specify the spec
    /// for the function.
    ///
    /// TODO: for `requires` we need to add the precondition that the leaf function
    /// is always within what we have defined.
    #[verifier::external_body]
    #[inline(always)]
    pub fn tdcall(args: &mut TdcallArgs) -> (ret: u64)
        ensures
            ret === 0 ==> args.rax == 1,
            ret === 1 ==> args.rcx == 0,
    {
        // The assembly code will handle the actual TDCALL call.
        unsafe { td_call_asm(args) >> 32 }
    }

    #[verifier::external]
    /// Check if the TDCALL instruction is supported by the CPU.
    pub fn check_tdcall() -> bool {
        let mut args = TdcallArgs::default();
        args.rax = TdcallNum::VpInfo as u64;

        // Call the TDCALL instruction and check if it returns 0 (success).
        Self::tdcall(&mut args) == 0
    }

    // pub fn veinfo()
    /// Get the VP (Virtual Processor) information.
    pub fn vpinfo() -> u64 {
        let mut args = TdcallArgs::default();
        args.rax = TdcallNum::VpInfo as u64;

        // Call the TDCALL instruction and check if it returns 0 (success).
        if Self::tdcall(&mut args) == 0 {
            args.rcx
        } else {
            0  // Return 0 on error

        }
    }
}

} // verus!
