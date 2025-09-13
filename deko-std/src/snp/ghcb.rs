use vstd::atomic::{
    PAtomicU16, PAtomicU32, PAtomicU64, PAtomicU8, PermissionU16, PermissionU32, PermissionU64,
    PermissionU8,
};
use vstd::prelude::*;

use crate::bits;
use crate::prelude::*;

deko_bitflags! {
    pub struct GHCBHvFeatures: u64 {
        const SEV_SNP                 = 0;
        const SEV_SNP_AP_CREATION     = 1;
        const SEV_SNP_RESTR_INJ       = 2;
        const SEV_SNP_RESTR_INJ_TIMER = 3;
        const APIC_ID_LIST            = 4;
        const SEV_SNP_MULTI_VMPL      = 5;
        const SEV_PAGE_STATE_CHANGE   = 6;
        const SEV_SNP_EXT_INTERRUPTS  = 9;
    }
}

verus! {

macro_rules! ghcb_getter {
    ($name:ident, $field:ident, $t:ty, $permname:ident) => {
        verus! {
            impl GuestHostCommucationBlock {
                #[verifier::external_body]
                fn $name(
                    ptr: DekoPPtr<Self>,
                    perm: Tracked<&DekoPointsTo<Self>>,
                ) -> (r: $t)
                {
                    // Check
                    let offset = core::mem::offset_of!(Self, $field);
                    if !Self::is_valid(ptr, perm, offset) {
                        vstd::vpanic!("Field not valid");
                    }

                    let Tracked(pperm) = Tracked::< $permname >::assume_new();
                    ptr.borrow(perm).$field.load(Tracked(&pperm))
                }
            }
        }
    };
}

macro_rules! ghcb_setter {
    ($name:ident, $field:ident, $t:ty, $permname:ident) => {
        verus! {
            impl GuestHostCommucationBlock {
                #[verifier::external_body]
                fn $name(
                    ptr: DekoPPtr<Self>,
                    perm: Tracked<DekoPointsTo<Self>>,
                    value: $t,
                ) -> Tracked<DekoPointsTo<Self>>
                {
                    let offset = core::mem::offset_of!(Self, $field);
                    let Tracked(mut perm) = perm;
                    let Tracked(mut pperm) = Tracked::< $permname >::assume_new();
                    let Tracked(perm) = ptr.update_in_place(Tracked(perm), |ghcb| {
                        unsafe { (*ghcb).$field.store(Tracked(&mut pperm), value); }
                    });

                    Self::set_valid(ptr, Tracked(perm), offset)
                }
            }
        }
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub enum GHCBExitCode {
    RDTSC = 0x6e,
    CPUID = 0x72,
    IOIO = 0x7b,
    MSR = 0x7c,
    VMMCALL = 0x81,
    RDTSCP = 0x87,
    MMIO_READ = 0x8000_0001,
    MMIO_WRITE = 0x8000_0002,
    SNP_PSC = 0x8000_0010,
    GUEST_REQUEST = 0x8000_0011,
    GUEST_EXT_REQUEST = 0x8000_0012,
    AP_CREATE = 0x80000013,
    HV_DOORBELL = 0x8000_0014,
    HV_IPI = 0x8000_0015,
    CONFIGURE_INT_INJ = 0x8000_001B,
    DISABLE_ALT_INJ = 0x8000_001C,
    SPECIFIC_EOI = 0x8000_001D,
}

/// Commands used to communicate withe GHCB MSR.
pub const SEV_INFO_REQ: u64 = 0x02;

pub const SEV_INFO_RESP: u64 = 0x01;

pub const SNP_REG_GHCB_GPA_REQ: u64 = 0x12;

pub const SNP_REG_GHCB_GPA_RESP: u64 = 0x13;

pub const SNP_STATE_CHANGE_REQ: u64 = 0x14;

pub const SNP_STATE_CHANGE_RESP: u64 = 0x15;

pub const SNP_HV_FEATURES_REQ: u64 = 0x80;

pub const SNP_HV_FEATURES_RESP: u64 = 0x81;

pub const TERM_REQ: u64 = 0x100;

#[repr(C)]
pub struct GuestHostCommucationBlock {
    _reserved: Array<PAtomicU8, 0xcb>,
    pub cpl: PAtomicU8,
    _reserved2: Array<PAtomicU8, 0x74>,
    pub xss: PAtomicU64,
    _reserved3: Array<PAtomicU8, 0x18>,
    pub dr7: PAtomicU64,
    _reserved4: Array<PAtomicU8, 0x90>,
    pub rax: PAtomicU64,
    _reserved5: Array<PAtomicU8, 0x100>,
    _reserved6: PAtomicU64,
    pub rcx: PAtomicU64,
    pub rdx: PAtomicU64,
    pub rbx: PAtomicU64,
    _reserved7: Array<PAtomicU8, 0x70>,
    /// Guest controlled exit code.
    pub sw_exitcode: PAtomicU64,
    /// Guest controlled exit info 1.
    pub sw_exitinfo1: PAtomicU64,
    /// Guest controlled exit info 2.
    pub sw_exitinfo2: PAtomicU64,
    /// Guest controlled additional information.
    pub sw_scratch: PAtomicU64,
    _reserved8: Array<PAtomicU8, 0x38>,
    pub xcr0: PAtomicU64,
    /// Bitmap to indicate valid qwords in the save state area
    /// starting from offset 0x000 through offset 0xe3f.
    pub valid_bitmap: Array<PAtomicU64, 0x2>,
    pub x87_state_gpa: PAtomicU64,
    _reserved9: Array<PAtomicU8, 0x3f8>,
    pub shared_buffer: Array<PAtomicU8, 0x7f0>,
    _reserved10: Array<PAtomicU8, 0x0a>,
    /// Version of the GHCB protocol used by the guest.
    pub ghcb_protocol_version: PAtomicU16,
    /// Provides an indicator of the usage and format of the GHCB:
    /// - 0x0000_0000: The GHCB page follows the format defined in
    ///                the AMD's manual.
    /// - Any other value can be used by the hypervisor, which can
    ///             determine its own format.
    pub ghcb_usage: PAtomicU32,
}

with_permission! {
    GuestHostCommucationBlock,
    self_perm: DekoPointsTo<GuestHostCommucationBlock>,
    cpl_perm: PermissionU8,
    xss_perm: PermissionU64,
    dr7_perm: PermissionU64,
    rax_perm: PermissionU64,
    rcx_perm: PermissionU64,
    rdx_perm: PermissionU64,
    rbx_perm: PermissionU64,
    sw_exitcode_perm: PermissionU64,
    sw_exitinfo1_perm: PermissionU64,
    sw_exitinfo2_perm: PermissionU64,
    sw_scratch_perm: PermissionU64,
    xcr0_perm: PermissionU64,
    valid_bitmap_perm: Ghost<Seq<PermissionU64>>,
    x87_state_gpa_perm: PermissionU64,
    ghcb_protocol_version_perm: PermissionU16,
    ghcb_usage_perm: PermissionU32,
}

impl WellFormed for GuestHostCommucationBlock {
    closed spec fn wf(&self) -> bool {
        true
    }
}

ghcb_setter!(set_cpl, cpl, u8, PermissionU8);

ghcb_setter!(set_xss, xss, u64, PermissionU64);

ghcb_setter!(set_rax, rax, u64, PermissionU64);

ghcb_getter!(get_rax, rax, u64, PermissionU64);

ghcb_setter!(set_rdx, rdx, u64, PermissionU64);

ghcb_getter!(get_rdx, rdx, u64, PermissionU64);

ghcb_setter!(set_exit_code_valid, sw_exitcode, u64, PermissionU64);

ghcb_setter!(set_exit_info_1, sw_exitinfo1, u64, PermissionU64);

ghcb_getter!(get_exit_info_1, sw_exitinfo1, u64, PermissionU64);

ghcb_setter!(set_exit_info_2, sw_exitinfo2, u64, PermissionU64);

ghcb_setter!(set_exit_scratch, sw_scratch , u64, PermissionU64);

ghcb_setter!(set_ghcb_usage, ghcb_usage, u32, PermissionU32);

ghcb_setter!(set_ghcb_protocol_version, ghcb_protocol_version, u16, PermissionU16);

impl GuestHostCommucationBlock {
    pub closed spec fn valid_bitmap(&self) -> Array<PAtomicU64, 0x2> {
        self.valid_bitmap
    }

    #[verifier::external_body]
    #[inline]
    pub fn set_valid_info(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        index: usize,
        mask: u64,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.wf_with_val(),
            perm.is_init(),
            perm.pptr() == ptr@,
            index < perm.value().valid_bitmap()@.len(),
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        ptr.update_in_place(
            Tracked(perm),
            |v|
                {
                    unsafe {
                        let Tracked(mut perm) = Tracked::<PermissionU64>::assume_new();
                        (*v).valid_bitmap.index(index).fetch_or(Tracked(&mut perm), mask);
                    }
                },
        )
    }

    #[verifier::external_body]
    pub fn is_valid(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<&DekoPointsTo<Self>>,
        offset: usize,
    ) -> (r: bool)
        requires
            perm.wf(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
            (offset >> 3) & 0x3f < 64,
            (offset >> 9 & 0x1) < perm.value().valid_bitmap()@.len(),
    {
        let valid_bitmap = &ptr.borrow(Tracked(&perm)).valid_bitmap;
        let bit: usize = (offset >> 3) & 0x3f;
        let index: usize = (offset >> 9) & 0x1;
        let mask: u64 = 1 << bit;

        let Tracked(perm) = Tracked::<PermissionU64>::assume_new();
        (valid_bitmap.index(index).load(Tracked(&perm)) & mask) == mask
    }

    /// Set something as valid in the bitmap.
    pub fn set_valid(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        offset: usize,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.wf_with_val(),
            perm.is_init(),
            perm.pptr() == ptr@,
            (offset >> 3) & 0x3f < 64,
            (offset >> 9 & 0x1) < perm.value().valid_bitmap()@.len(),
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        let bit: usize = (offset >> 3) & 0x3f;
        let index: usize = (offset >> 9) & 0x1;
        let mask: u64 = 1 << bit;

        Self::set_valid_info(ptr, Tracked(perm), index, mask)
    }

    /// Performs a VMGEXIT.
    #[verifier::external_body]
    pub fn vmgexit(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        reason: GHCBExitCode,
        info_1: u64,
        info_2: u64,
    ) -> (r: Tracked<DekoPointsTo<Self>>)
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        // GHCB is version 2
        let Tracked(perm) = Self::set_ghcb_protocol_version(ptr, Tracked(perm), 2);
        // Set usage to 0
        let Tracked(perm) = Self::set_ghcb_usage(ptr, Tracked(perm), 0);
        // Set exit code and infos
        let Tracked(perm) = Self::set_exit_code_valid(ptr, Tracked(perm), reason as _);
        let Tracked(perm) = Self::set_exit_info_1(ptr, Tracked(perm), info_1);
        let Tracked(perm) = Self::set_exit_info_2(ptr, Tracked(perm), info_2);

        let ghcb_pa = ptr.addr() as u64;
        no_irq_zone(
            ||
                {
                    write_msr(MSR_AMD64_SEV_ES_GHCB, ghcb_pa);
                },
        );
        raw_vmgexit();

        let sw_exit_info_1 = Self::get_exit_info_1(ptr, Tracked(&perm));
        if sw_exit_info_1 != 0 {
            vstd::vpanic!("GHCB VMGEXIT failed: {}", sw_exit_info_1);
        }

        Tracked(perm)
    }

    #[verifier::external_body]
    pub fn clear(ptr: DekoPPtr<Self>, Tracked(perm): Tracked<DekoPointsTo<Self>>) -> (r: Tracked<
        DekoPointsTo<Self>,
    >)
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
        ensures
            r@.wf(),
            r@.wf_with_val(),
            r@.is_init(),
            r@.pptr() == ptr@,
    {
        let off = core::mem::offset_of!(Self, valid_bitmap);
        let Tracked(perm) = ptr.update_in_place(
            Tracked(perm),
            |ghcb|
                {
                    unsafe {
                        let Tracked(mut pperm) = Tracked::<PermissionU64>::assume_new();
                        (*ghcb).valid_bitmap.index(0).store(Tracked(&mut pperm), 0);
                        (*ghcb).valid_bitmap.index(1).store(Tracked(&mut pperm), 0);
                    }
                },
        );

        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), off);
        let Tracked(perm) = Self::set_valid(ptr, Tracked(perm), off + 8);

        Tracked(perm)
    }

    pub fn rdtsc(ptr: DekoPPtr<Self>, Tracked(perm): Tracked<DekoPointsTo<Self>>) -> (r: (u64, Tracked<DekoPointsTo<Self>>))
        requires
            perm.wf(),
            perm.is_init(),
            perm.wf_with_val(),
            perm.pptr() == ptr@,
    {
        let Tracked(perm) = Self::clear(ptr, Tracked(perm));
        let Tracked(perm) = Self::vmgexit(ptr, Tracked(perm), GHCBExitCode::RDTSC, 0, 0);

        let rax = Self::get_rax(ptr, Tracked(&perm));
        let rdx = Self::get_rdx(ptr, Tracked(&perm));

        let val = (((rdx as u32 as u64) << 32)) as u64 | rax;

        (val, Tracked(perm))
    }

    #[verifier::external_body]
    pub fn ioin(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        port: u16,
        size: u8,
    ) -> (r: u64) {
        0
    }

    #[verifier::external_body]
    pub fn ioout(
        ptr: DekoPPtr<Self>,
        Tracked(perm): Tracked<DekoPointsTo<Self>>,
        port: u16,
        value: u64,
        size: u8,
    ) {
        let mut info: u64 = 0;  // OUT instruction

        info |= (port as u64) << 16;
        info |= 1 << ((size as u64) + 3);

        let Tracked(perm) = Self::set_rax(ptr, Tracked(perm), value);
        Self::vmgexit(ptr, Tracked(perm), GHCBExitCode::IOIO, info, 0);
    }
}

} // verus!
