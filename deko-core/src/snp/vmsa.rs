use core::ops::Index;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::array::Array;
use deko_std::bits::bit_u32_and_auto;
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M};
use deko_std::prelude::VirtAddr;
use deko_std::ptr::{addr_of_ref, DekoPPtr, DekoPointsTo};
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, with_permission};
use vstd::prelude::*;

use crate::cpu::gdt::GLOBAL_GDT;
use crate::cpu::regs::{
    read_cr0, read_cr4, read_efer, DEKO_DS, DEKO_DS_ATTRIBUTES, DEKO_TR_ATTRIBUTES, DEKO_TSS,
};
use crate::cpu::X86Tss;
use crate::mm::DEKO_FRAME_ALLOCATOR;
use crate::snp::{
    rmpadjust, DekoCpuCtxPermission, PageTablePermission, RmpFlags, Rmp_ALL_BITS, SnpStatusFlags,
    BIT_VMSA,
};
use crate::{die, kerror, kunimplemented};

verus! {

#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VmsaInitialContext {
    pub rip: u64,
    pub rsp: u64,
    pub rflags: u64,
    pub cs: VMSASegment,
    pub ds: VMSASegment,
    pub es: VMSASegment,
    pub fs: VMSASegment,
    pub gs: VMSASegment,
    pub ss: VMSASegment,
    pub tr: VMSASegment,
    pub ldtr: VMSASegment,
    pub idtr: VmsaTableRegister,
    pub gdtr: VmsaTableRegister,
    pub efer: u64,
    pub cr0: u64,
    pub cr3: u64,
    pub cr4: u64,
    pub pat: u64,
}

#[repr(C, packed)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VMSASegment {
    pub selector: u16,
    pub flags: u16,
    pub limit: u32,
    pub base: u64,
}

#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VmsaTableRegister {
    pub _rsvd: [u16; 3],
    pub limit: u16,
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
    pub page: DekoPPtr<[VMSA; 2]>,
    pub idx: usize,
}

impl WellFormed for VmsaPage {
    open spec fn wf(&self) -> bool {
        &&& self.idx < 2
    }
}

impl WellFormed for VMSA {
    open spec fn wf(&self) -> bool {
        true
    }
}

with_permission! {
    VmsaPage,
    ptr_perm: DekoPointsTo<[VMSA; 2]>,
}

with_atomic_pred! {
    VmsaPage,
    VmsaPagePermission,
    fields: { page },
    perm_fields: { ptr_perm },
    ptr_perm.pptr() == page.view() && ptr_perm.is_init() && ptr_perm.wf()
}

#[verus_verify]
impl VmsaInitialContext {
    /// Constructs a new initial VMSA context from the given RIP and CSS top.
    #[verus_spec(r =>

    )]
    pub fn new_with(rip: u64, css_top: u64, cr3: u64, tss: &X86Tss) -> Self {
        let ds = VMSASegment {
            selector: DEKO_DS,
            flags: DEKO_DS_ATTRIBUTES,
            limit: 0xffff_ffff,
            base: 0,
        };
        let cs = VMSASegment {
            selector: DEKO_DS,
            flags: DEKO_DS_ATTRIBUTES,
            limit: 0xffff_ffff,
            base: 0,
        };
        let tr = VMSASegment {
            selector: DEKO_TSS,
            flags: DEKO_TR_ATTRIBUTES,
            limit: core::mem::size_of::<X86Tss>() as u32,
            base: addr_of_ref(tss) as u64,
        };

        Self {
            rip,
            rsp: css_top,
            rflags: 0x2,
            cs,
            ss: ds.clone(),
            ds: ds.clone(),
            es: ds.clone(),
            fs: ds.clone(),
            gs: ds.clone(),
            cr0: read_cr0().bits(),
            cr4: read_cr4().bits(),
            cr3,
            tr,
            efer: read_efer().bits(),
            ldtr: VMSASegment { selector: 0, flags: 0, limit: 0, base: 0 },
            gdtr: VmsaTableRegister {
                _rsvd: [0;3],
                limit: 0,  // fix this.
                base: 0,
            },
            idtr: VmsaTableRegister {
                _rsvd: [0;3],
                limit: 0,  // fix this.
                base: 0,
            },
            pat: 0x0007040600070406u64,
        }
    }
}

#[verus_verify]
impl VmsaPage {
    /// Allocates a VMSA page.
    #[verus_spec(r =>
        with
            Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
                -> perm: Tracked<VmsaPagePermission>,
        requires
            rmp.wf(),
            rmp.bits() & Rmp_ALL_BITS == rmp.bits(),
            old(pgtable_perm).wf(),
        ensures
            old(pgtable_perm).pgtable_perm == pgtable_perm.pgtable_perm,
            old(pgtable_perm).private_bit == pgtable_perm.private_bit,
            old(pgtable_perm).shared_bit == pgtable_perm.shared_bit,
            old(pgtable_perm).mapping_space == pgtable_perm.mapping_space,
            pgtable_perm.pgtable_perm.wf(),
            pgtable_perm.wf(),
            pgtable_perm.pgtable_perm.is_init(),
            perm@.ptr_perm.wf(),
            perm@.ptr_perm.pptr() == r.page@,
            perm@.ptr_perm.is_init(),
            r.wf(),
    )]
    pub fn alloc(rmp: RmpFlags) -> Self {
        broadcast use RmpFlags::lemma_each_bit_is_valid;

        let (page, Tracked(perm)) = boxed_ptr!([VMSA; 2], &DEKO_FRAME_ALLOCATOR.0);

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
        let vaddr = VirtAddr(page.addr() as u64 + (idx as u64) * PAGE_SIZE);
        let flags = RmpFlags::from_bits_truncate(rmp.bits() | BIT_VMSA);

        proof {
            assert(flags.bits() & Rmp_ALL_BITS == flags.bits()) by {
                bit_u32_and_auto();
            }
            assume(perm.is_init());
            assume(pgtable_perm.mapped(vaddr));
        }

        // Perform a RMPADJUST to set the page as VMSA.
        rmpadjust(vaddr, PAGE_SIZE, flags, Tracked(pgtable_perm));

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

    /// Initializes the VMSA page from the initial context.
    ///
    /// # Note
    ///
    /// This function is marked as `external_body` because it involves low-level
    /// operations that cannot be directly verified by Verus. We can copy the whole
    /// page onto the stack which will then be overflown. This requires some unsafe
    /// pointer manipulations instead. However, since we hold the permission to the VMSA
    /// page, we can ensure that the operation is safe and does not violate memory safety.
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(perm).ptr_perm.wf(),
            old(perm).ptr_perm.pptr() == self.page@,
            self.wf(),
        ensures
            perm.ptr_perm.wf(),
            perm.ptr_perm.pptr() == self.page@,
            perm.ptr_perm.is_init(),
    )]
    pub fn init_from(&self, ctx: &VmsaInitialContext) -> u64 {
        let this = unsafe {
            &mut *(self.page.borrow(Tracked(&perm.ptr_perm)).as_ptr().wrapping_add(
                self.idx * PAGE_SIZE as usize,
            ) as *mut VMSA)
        };

        this.es = ctx.es;
        this.cs = ctx.cs;
        this.ss = ctx.ss;
        this.ds = ctx.ds;
        this.fs = ctx.fs;
        this.gs = ctx.gs;
        this.tr = ctx.tr;

        this.rip = ctx.rip;
        this.rsp = ctx.rsp;
        this.rflags = ctx.rflags;

        this.gdt = VMSASegment {
            selector: 0,
            flags: 0,
            limit: ctx.gdtr.limit as u32,
            base: ctx.gdtr.base,
        };
        this.idt = VMSASegment {
            selector: 0,
            flags: 0,
            limit: ctx.idtr.limit as u32,
            base: ctx.idtr.base,
        };

        this.cr0 = ctx.cr0;
        this.cr3 = ctx.cr3;
        this.cr4 = ctx.cr4;
        this.efer = ctx.efer;

        this.g_pat = ctx.pat;
        this.dr6 = 0xffff_0ff0;
        this.dr7 = 0x400;
        this.xcr0 = 0x1;
        this.mxcsr = 0x1f80;
        this.x87_fcw = 0x404;
        this.x87_fsw = 0x5555;
        this.vmpl = 0;
        this.vtom = 0;  // unsupported.
        this.sev_features = SnpStatusFlags::get_status().bits() as _;

        // Being lazy
        this.sev_features
    }
}

} // verus!
