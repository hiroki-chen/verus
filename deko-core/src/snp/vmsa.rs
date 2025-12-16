use deko_macros::DekoDebug;
use deko_std::array::Array;
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::ptr::{DekoPPtr, DekoPointsTo};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;

use crate::mm::DEKO_FRAME_ALLOCATOR;
use crate::snp::{rmpadjust, DekoCpuCtxPermission, RmpFlags, Rmp_ALL_BITS};
use crate::{die, kerror, kunimplemented};

verus! {

#[repr(C, packed)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VMSASegment {
    pub selector: u16,
    pub flags: u16,
    pub limit: u32,
    pub base: u64,
}

#[repr(u64)]
#[derive(DekoDebug, Clone, Copy)]
pub enum VmsaEventType {
    Interrupt = 0,
    NMI = 2,
    Exception = 3,
    SoftwareInterrupt = 4,
}

#[repr(transparent)]
#[derive(DekoDebug, Clone, Copy)]
pub struct GuestVMExit(pub u64);

#[repr(transparent)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VmsaEventInject(pub u64);

#[repr(transparent)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VIntrCtrl(pub u64);

#[repr(C, packed)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VMSA {
    pub es: VMSASegment,
    pub cs: VMSASegment,
    pub ss: VMSASegment,
    pub ds: VMSASegment,
    pub fs: VMSASegment,
    pub gs: VMSASegment,
    pub gdt: VMSASegment,
    pub ldt: VMSASegment,
    pub idt: VMSASegment,
    pub tr: VMSASegment,
    pub pl0_ssp: u64,
    pub pl1_ssp: u64,
    pub pl2_ssp: u64,
    pub pl3_ssp: u64,
    pub u_cet: u64,
    pub reserved_0c8: u16,
    pub vmpl: u8,
    pub cpl: u8,
    pub reserved_0cc: u32,
    pub efer: u64,
    pub reserved_0d8: Array<u8, 104>,
    pub xss: u64,
    pub cr4: u64,
    pub cr3: u64,
    pub cr0: u64,
    pub dr7: u64,
    pub dr6: u64,
    pub rflags: u64,
    pub rip: u64,
    pub dr0: u64,
    pub dr1: u64,
    pub dr2: u64,
    pub dr3: u64,
    pub dr0_mask: u64,
    pub dr1_mask: u64,
    pub dr2_mask: u64,
    pub dr3_mask: u64,
    pub reserved_1c0: Array<u8, 24>,
    pub rsp: u64,
    pub s_cet: u64,
    pub ssp: u64,
    pub isst_addr: u64,
    pub rax: u64,
    pub star: u64,
    pub lstar: u64,
    pub cstar: u64,
    pub sfmask: u64,
    pub kernel_gs_base: u64,
    pub sysenter_cs: u64,
    pub sysenter_esp: u64,
    pub sysenter_eip: u64,
    pub cr2: u64,
    pub reserved_248: Array<u8, 32>,
    pub g_pat: u64,
    pub dbgctl: u64,
    pub br_from: u64,
    pub br_to: u64,
    pub last_excp_from: u64,
    pub last_excp_to: u64,
    pub reserved_298: Array<u8, 72>,
    pub reserved_2e0: u64,
    pub pkru: u32,
    pub reserved_2ec: u32,
    pub guest_tsc_scale: u64,
    pub guest_tsc_offset: u64,
    pub reg_prot_nonce: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbx: u64,
    pub reserved_320: u64,
    pub rbp: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,
    pub reserved_380: Array<u8, 16>,
    pub guest_exitinfo1: u64,
    pub guest_exitinfo2: u64,
    pub guest_exitintinfo: VmsaEventInject,
    pub guest_nrip: u64,
    pub sev_features: u64,
    pub vintr_ctrl: VIntrCtrl,
    pub guest_exit_code: GuestVMExit,
    pub vtom: u64,
    pub tlb_id: u64,
    pub pcpu_id: u64,
    pub event_inj: VmsaEventInject,
    pub xcr0: u64,
    pub reserved_3f0: Array<u8, 16>,
    pub x87_dp: u64,
    pub mxcsr: u32,
    pub x87_ftw: u16,
    pub x87_fsw: u16,
    pub x87_fcw: u16,
    pub x87_fop: u16,
    pub x87_ds: u16,
    pub x87_cs: u16,
    pub x87_rip: u64,
    pub fpreg_x87: Array<u8, 80>,
    pub fpreg_xmm: Array<u8, 256>,
    pub fpreg_ymm: Array<u8, 256>,
    pub lbr_stack: Array<u8, 256>,
    pub lbr_select: u64,
    pub ibs_fetch_ctl: u64,
    pub ibs_fetch_linaddr: u64,
    pub ibs_op_ctl: u64,
    pub ibs_op_rip: u64,
    pub ibs_op_data: u64,
    pub ibs_op_data2: u64,
    pub ibs_op_data3: u64,
    pub ibs_dc_linaddr: u64,
    pub bp_ibstgt_rip: u64,
    pub ic_ibs_extd_ctl: u64,
    pub reserved_7c8: Array<u8, 2104>,
}

#[derive(DekoDebug)]
pub struct VmsaPage {
    pub page: DekoPPtr<Array<u8, 4096>>,
    pub idx: usize,
}

impl WellFormed for VmsaPage {
    open spec fn wf(&self) -> bool {
        true
    }
}

with_permission! {
    VmsaPage,
    ptr_perm: DekoPointsTo<Array<u8, 4096>>,
}

#[verus_verify]
impl VmsaPage {
    /// Allocates a VMSA page.
    #[verus_spec(r =>
        with
            -> perm: Tracked<VmsaPagePermission>,
        requires
            rmp.wf(),
            rmp.bits() & Rmp_ALL_BITS == rmp.bits(),
        ensures
            perm@.ptr_perm.wf(),
            perm@.ptr_perm.pptr() == r.page@,
            perm@.ptr_perm.is_init(),
    )]
    pub fn alloc(rmp: RmpFlags) -> Self {
        let (page, Tracked(perm)) = boxed_ptr!(Array<u8, 4096>, &DEKO_FRAME_ALLOCATOR.0);
        assume(perm.is_init());

        // Make sure the VMSA page is not 2M-aligned.
        // To ensure this property, we allocate 2 VMSAs.
        let idx = if page.addr() as u64 % PAGE_SIZE_2M == 0 {
            1
        } else {
            0
        };

        if page.addr() as u64 >= u64::MAX - PAGE_SIZE {
            kerror!("VMSA page allocation overflow");
            die("aa");
        }
        let vaddr = page.addr() as u64 + (idx as u64) * PAGE_SIZE;

        // Perform a RMPADJUST to set the page as VMSA.
        // FIXME: The input param takes a dekoctxpermission.
        // need to change it; perhaps need a rmptable_perm?

        // rmpadjust(vaddr, PAGE_SIZE, Tracked(cpu));

        proof_with!(|= Tracked(
            VmsaPagePermission {
                ptr_perm: perm,
            }
        ));
        Self {
            page,
            idx,  // indicate which VMSA we use
        }
    }

    /// Initializes the VMSA page.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(perm).ptr_perm.wf(),
            old(perm).ptr_perm.pptr() == self.page@,
    )]
    pub fn init(&self) {
        // let VMSA { es, cs, ss, ds, fs, gs, gdt, ldt, idt, tr, pl0_ssp, pl1_ssp, pl2_ssp, pl3_ssp, u_cet, reserved_0c8, vmpl, cpl, reserved_0cc, efer, reserved_0d8, xss, cr4, cr3, cr0, dr7, dr6, rflags, rip, dr0, dr1, dr2, dr3, dr0_mask, dr1_mask, dr2_mask, dr3_mask, reserved_1c0, rsp, s_cet, ssp, isst_addr, rax, star, lstar, cstar, sfmask, kernel_gs_base, sysenter_cs, sysenter_esp, sysenter_eip, cr2, reserved_248, g_pat, dbgctl, br_from, br_to, last_excp_from, last_excp_to, reserved_298, reserved_2e0, pkru, reserved_2ec, guest_tsc_scale, guest_tsc_offset, reg_prot_nonce, rcx, rdx, rbx, reserved_320, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15, reserved_380, guest_exitinfo1, guest_exitinfo2, guest_exitintinfo, guest_nrip, sev_features, vintr_ctrl, guest_exit_code, vtom, tlb_id, pcpu_id, event_inj, xcr0, reserved_3f0, x87_dp, mxcsr, x87_ftw, x87_fsw, x87_fcw, x87_fop, x87_ds, x87_cs, x87_rip, fpreg_x87, fpreg_xmm, fpreg_ymm, lbr_stack, lbr_select, ibs_fetch_ctl, ibs_fetch_linaddr, ibs_op_ctl, ibs_op_rip, ibs_op_data, ibs_op_data2, ibs_op_data3, ibs_dc_linaddr, bp_ibstgt_rip, ic_ibs_extd_ctl, reserved_7c8 };
    }
}

} // verus!
