use core::ops::Index;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::address::{create_paddr_range, PhysAddr};
use deko_std::array::Array;
use deko_std::bits::bit_u32_and_auto;
use deko_std::boot::IgvmParams;
use deko_std::mem::{PAGE_SIZE, PAGE_SIZE_2M, PERCPU_VMSA_BASE};
use deko_std::prelude::{VirtAddr, VADDR_UPPER_MASK};
use deko_std::ptr::{addr_of_ref, DekoPPtr, DekoPointsTo};
use deko_std::sync::DekoAtomicData;
use deko_std::wf::WellFormed;
use deko_std::{boxed_ptr, trace_is_enabled, with_permission};
use vstd::prelude::*;

use crate::cpu::gdt::GLOBAL_GDT;
use crate::cpu::idt::GLOBAL_IDT;
use crate::cpu::regs::{
    read_cr0, read_cr4, read_efer, DEKO_CS, DEKO_CS_ATTRIBUTES, DEKO_DS, DEKO_DS_ATTRIBUTES,
    DEKO_TR_ATTRIBUTES, DEKO_TSS,
};
use crate::cpu::tlb::flush_tlb_global_percpu;
use crate::cpu::{DekoCpuCtx, X86Tss};
use crate::mm::paging::PageTable;
use crate::mm::vm::TempMapping;
use crate::mm::DEKO_FRAME_ALLOCATOR_FULL;
use crate::policy::{DekoMsrInterceptVec0, DekoSyscallBody};
use crate::snp::{
    rmpadjust, DekoCpuCtxPermission, PageTablePermission, RmpFlags, Rmp_ALL_BITS, SnpStatusFlags,
    ALT_INJ, BIT_VMSA, GUEST_MSR_INTERCEPT, REST_INJ, VMPL1_MAGIC_KERN, VMPL_GUEST_DEKO_MONITOR,
};
use crate::{die, kdebug, kerror, kinfo, kunimplemented, kwarn};

const _: () = {
    assert!(core::mem::size_of::<VMSASegment>() == 0x10);
    assert!(core::mem::size_of::<VmsaTableRegister>() == 0x10);
    assert!(core::mem::size_of::<VMSA>() == 4096);

    assert!(core::mem::offset_of!(VMSA, intercept_vecs) == 0x900);
    assert!(core::mem::offset_of!(VMSA, intercept_msr_vecs) == 0x920);
};

verus! {

global layout VMSA is size == 4096;

global layout VMSASegment is size == 16;

global layout VmsaTableRegister is size == 16;

#[inline]
fn real_mode_code_segment(rip: u64) -> VMSASegment {
    VMSASegment { selector: 0xf000, base: rip & 0xffff_0000u64, limit: 0xffff, flags: 0x9b }
}

#[inline]
fn real_mode_data_segment() -> VMSASegment {
    VMSASegment { selector: 0, flags: 0x93, limit: 0xFFFF, base: 0 }
}

#[inline]
fn real_mode_sys_seg(flags: u16) -> VMSASegment {
    VMSASegment { selector: 0, base: 0, limit: 0xffff, flags }
}

#[inline]
pub fn guest_user_code_segment() -> VMSASegment {
    VMSASegment { selector: 0x33, base: 0, limit: 0xffff_ffff, flags: 0x2FB }
}

#[inline]
pub fn guest_user_stack_segment() -> VMSASegment {
    // 0xCF3 (G=1, B=1, P=1, DPL=3, S=1, Type=3)
    VMSASegment { selector: 0x2B, base: 0, limit: 0xffff_ffff, flags: 0xCF3 }
}

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
    #[deko(hex)]
    pub selector: u16,
    #[deko(hex)]
    pub flags: u16,
    #[deko(hex)]
    pub limit: u32,
    #[deko(hex)]
    pub base: u64,
}

#[repr(C)]
#[derive(DekoDebug, Clone, Copy)]
pub struct VmsaTableRegister {
    #[deko(skip)]
    pub _rsvd: [u16; 3],
    #[deko(hex)]
    pub limit: u16,
    #[deko(hex)]
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

/// The Virtual Machine Save Area (VMSA) structure for AMD SEV-SNP.
/// See https://docs.amd.com/v/u/en-US/24593_3.43 and `struct sev_es_save_area` from
/// `arch/x86/include/asm/svm.c` in the Linux kernel source.
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
    #[deko(hex)]
    pub pl0_ssp: u64,
    #[deko(hex)]
    pub pl1_ssp: u64,
    #[deko(hex)]
    pub pl2_ssp: u64,
    #[deko(hex)]
    pub pl3_ssp: u64,
    #[deko(hex)]
    pub u_cet: u64,
    #[deko(skip)]
    pub reserved_0c8: u16,
    pub vmpl: u8,
    pub cpl: u8,
    #[deko(skip)]
    pub reserved_0cc: u32,
    #[deko(hex)]
    pub efer: u64,
    #[deko(skip)]
    pub reserved_0d8: Array<u8, 104>,
    pub xss: u64,
    #[deko(hex)]
    pub cr4: u64,
    #[deko(hex)]
    pub cr3: u64,
    #[deko(hex)]
    pub cr0: u64,
    #[deko(hex)]
    pub dr7: u64,
    #[deko(hex)]
    pub dr6: u64,
    #[deko(hex)]
    pub rflags: u64,
    #[deko(hex)]
    pub rip: u64,
    pub dr0: u64,
    pub dr1: u64,
    pub dr2: u64,
    pub dr3: u64,
    pub dr0_mask: u64,
    pub dr1_mask: u64,
    pub dr2_mask: u64,
    pub dr3_mask: u64,
    #[deko(skip)]
    pub reserved_1c0: Array<u8, 24>,
    #[deko(hex)]
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
    #[deko(skip)]
    pub reserved_248: Array<u8, 32>,
    pub g_pat: u64,
    pub dbgctl: u64,
    pub br_from: u64,
    pub br_to: u64,
    pub last_excp_from: u64,
    pub last_excp_to: u64,
    #[deko(skip)]
    pub reserved_298: Array<u8, 72>,
    #[deko(skip)]
    pub reserved_2e0: u64,
    pub pkru: u32,
    pub tsc_aux: u32,
    pub guest_tsc_scale: u64,
    pub guest_tsc_offset: u64,
    pub reg_prot_nonce: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbx: u64,
    #[deko(skip)]
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
    #[deko(skip)]
    pub reserved_380: Array<u8, 16>,
    pub guest_exitinfo1: u64,
    pub guest_exitinfo2: u64,
    pub guest_exitintinfo: VmsaEventInject,
    pub guest_nrip: u64,
    #[deko(hex)]
    pub sev_features: u64,
    pub vintr_ctrl: VIntrCtrl,
    pub guest_exit_code: GuestVMExit,
    pub vtom: u64,
    pub tlb_id: u64,
    pub pcpu_id: u64,
    pub event_inj: VmsaEventInject,
    pub xcr0: u64,
    #[deko(skip)]
    pub reserved_3f0: Array<u8, 16>,
    pub x87_dp: u64,
    #[deko(hex)]
    pub mxcsr: u32,
    #[deko(hex)]
    pub x87_ftw: u16,
    pub x87_fsw: u16,
    #[deko(hex)]
    pub x87_fcw: u16,
    pub x87_fop: u16,
    pub x87_ds: u16,
    pub x87_cs: u16,
    pub x87_rip: u64,
    #[deko(skip)]
    pub fpreg_x87: Array<u8, 80>,
    #[deko(skip)]
    pub fpreg_xmm: Array<u8, 256>,
    #[deko(skip)]
    pub fpreg_ymm: Array<u8, 256>,
    #[deko(skip)]
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
    #[deko(skip)]
    pub _reserved_7c8: Array<u8, 312>,
    /// Support for guest intercept controls.
    /// When the GuestInterceptCtl bit in SEV_FEATURES is set,
    /// an instruction, exception or interrupt event will be intecepted
    /// if the corresponding bit in this field is set.
    pub intercept_vecs: [u32; 8],
    /// Support for guest intercept MSR R/W controls.
    /// Currently the last vector is reserved (INTERCEPT_MSR_VEC3).
    pub intercept_msr_vecs: [u64; 4],
    /// AVX512, ZMM, and opmask registers (not used currently).
    #[deko(skip)]
    pub reserved_940: Array<u8, 1728>,
}

#[derive(DekoDebug)]
pub struct VmsaPage {
    pub page: DekoPPtr<[VMSA; 2]>,
    pub idx: usize,
}

impl WellFormed for VmsaPage {
    open spec fn wf(&self) -> bool {
        &&& self.idx < 2
        &&& self.page.addr() + 2 * PAGE_SIZE <= u64::MAX
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
    ptr_perm.pptr() == page.view() && ptr_perm.is_init() && ptr_perm.wf() && data.wf()
}

#[verus_verify]
impl VMSA {
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(cpu_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(cpu_perm).wf(),
            old(cpu_perm).is_init(),
            old(cpu_perm).pptr() == ptr@,
        ensures
            cpu_perm.wf(),
            cpu_perm.is_init(),
            cpu_perm.pptr() == ptr@,
    )]
    pub fn copy_system_call_registers(ptr: DekoPPtr<Self>, syscall_body: &DekoSyscallBody) {
        unsafe {
            let struct_ptr = ptr.addr() as *mut Self;

            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*struct_ptr).rax),
                syscall_body.rax,
            );
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*struct_ptr).rcx),
                syscall_body.rcx,
            );
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*struct_ptr).rdx),
                syscall_body.rdx,
            );
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*struct_ptr).rdi),
                syscall_body.rdi,
            );
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*struct_ptr).rsi),
                syscall_body.rsi,
            );
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*struct_ptr).r8), syscall_body.r8);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*struct_ptr).r9), syscall_body.r9);
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*struct_ptr).r10),
                syscall_body.r10,
            );
        }
    }

    /// Enables the VMSA by setting the SVME bit in the EFER register.
    ///
    /// This function modifies the EFER (Extended Feature Enable Register) field
    /// of the VMSA to set the SVME (Secure Virtual Machine Enable) bit (bit 12).
    /// This is necessary to mark the VMSA as valid for secure execution.
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.value().efer & 0x1000 != 0,
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn enable(ptr: DekoPPtr<Self>) {
        unsafe {
            // 1. Get the raw pointer to the struct.
            // DO NOT convert this to &mut Self.
            let struct_ptr = ptr.addr() as *mut Self;

            // 2. Calculate the pointer to the 'efer' field specifically.
            // 'addr_of_mut!' computes the offset without creating an intermediate reference
            // to the struct, avoiding issues with unaligned/packed data or MMIO restrictions.
            let efer_field_ptr = core::ptr::addr_of_mut!((*struct_ptr).efer);

            // 3. Use a Volatile Read-Modify-Write.
            // This guarantees the compiler emits load/store instructions, does not optimize them away,
            // and does not try to use 'memcpy' or wide registers.
            let v = core::ptr::read_unaligned(efer_field_ptr) | (1 << 12);
            core::ptr::write_unaligned(efer_field_ptr, v);
        }
    }

    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn check_and_clear_pending_interrupt_event(ptr: DekoPPtr<Self>) -> u8 {
        unsafe {
            let struct_ptr = ptr.addr() as *mut Self;

            let event_inj_ptr = core::ptr::addr_of_mut!((*struct_ptr).event_inj);
            let raw_val = core::ptr::read_unaligned(event_inj_ptr).0;
            let is_valid = (raw_val & (1 << 31)) != 0;
            let event_type = (raw_val >> 8) & 0b111;
            let is_interrupt_type = event_type == 0;

            if event_type == 0  /* is interrupt? */
             && is_valid {
                // clear it.
                core::ptr::write_unaligned(event_inj_ptr, VmsaEventInject(0));
                // fetch the vector.
                (raw_val & 0xff as u64) as u8
            } else {
                0
            }
        }
    }

    #[verus_spec()]
    pub fn err_dump_vmsa() {
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        proof_with!(Tracked(&cpu_perm) => Tracked(vmsa_perm));
        let this_vmsa = VMSA::this_vmsa(cpu);

        let vmsa = this_vmsa.borrow(Tracked(&vmsa_perm));

        kerror!("VMSA dump:", vmsa);
    }

    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn check_and_clear_pending_virtual_interrupt(ptr: DekoPPtr<Self>) -> u8 {
        unsafe {
            let struct_ptr = ptr.addr() as *mut Self;

            let vintr_ctrl_ptr = core::ptr::addr_of_mut!((*struct_ptr).vintr_ctrl);
            let raw_val = core::ptr::read_unaligned(vintr_ctrl_ptr).0;

            let v_irq_mask = 1u64 << 8;
            if (raw_val & v_irq_mask) != 0 {
                let new_val = raw_val & !v_irq_mask;
                core::ptr::write_unaligned(vintr_ctrl_ptr, VIntrCtrl(new_val));

                ((raw_val >> 32) & 0xff) as u8
            } else {
                0
            }
        }
    }

    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn deliver_interrupt_immediately(ptr: DekoPPtr<Self>, irq: u8) -> bool {
        unsafe {
            let struct_ptr = ptr.addr() as *mut Self;
            let event_inj_ptr = core::ptr::addr_of_mut!((*struct_ptr).event_inj);

            let raw_val = core::ptr::read_unaligned(event_inj_ptr).0;
            let valid = (raw_val & (1 << 31)) != 0;

            if valid {
                false
            } else {
                let mut v = 0;
                v |= (1u64 << 31);  // valid
                // set irq.
                v |= (irq as u64) & 0xff;
                // set type to interrupt.
                v |= (VmsaEventType::Interrupt as u64) << 8;
                core::ptr::write_unaligned(event_inj_ptr, VmsaEventInject(v));
                true
            }
        }
    }

    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.value().lstar == lstar,
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn set_lstar(ptr: DekoPPtr<Self>, lstar: u64) {
        unsafe {
            // 1. Get the raw pointer to the struct.
            // DO NOT convert this to &mut Self.
            let struct_ptr = ptr.addr() as *mut Self;

            // 2. Calculate the pointer to the 'lstar' field specifically.
            // 'addr_of_mut!' computes the offset without creating an intermediate reference
            // to the struct, avoiding issues with unaligned/packed data or MMIO restrictions.
            let lstar_field_ptr = core::ptr::addr_of_mut!((*struct_ptr).lstar);

            // 3. Use a Volatile Write.
            // This guarantees the compiler emits a store instruction, does not optimize it away,
            // and does not try to use 'memcpy' or wide registers.
            core::ptr::write_unaligned(lstar_field_ptr, lstar);
        }
    }

    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.value().rax == value,
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn set_rax(ptr: DekoPPtr<Self>, value: u64) {
        unsafe {
            // 1. Get the raw pointer to the struct.
            // DO NOT convert this to &mut Self.
            let struct_ptr = ptr.addr() as *mut Self;

            // 2. Calculate the pointer to the 'rax' field specifically.
            // 'addr_of_mut!' computes the offset without creating an intermediate reference
            // to the struct, avoiding issues with unaligned/packed data or MMIO restrictions.
            let rax_field_ptr = core::ptr::addr_of_mut!((*struct_ptr).rax);

            // 3. Use a Volatile Write.
            // This guarantees the compiler emits a store instruction, does not optimize it away,
            // and does not try to use 'memcpy' or wide registers.
            core::ptr::write_unaligned(rax_field_ptr, value);
        }
    }

    /// Prepares the VMSA for a new user application by initializing
    /// necessary fields.
    ///
    /// This function overwrites the system call handler for the new application.
    /// Note that this function requires that the `vmpl2_vmsa` runs currently at
    /// CPL3 so that we will not accidentally set up a VMSA that cannot be
    /// entered due to privilege level issues.
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
            Tracked(vmpl2_vmsa_perm): Tracked<&DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
            vmpl2_vmsa_perm.wf(),
            vmpl2_vmsa_perm.is_init(),
            vmpl2_vmsa_perm.pptr() == vmpl2_vmsa@,
            deko_ifc_handler@ >= VADDR_UPPER_MASK,
            deko_ifc_handler@ % PAGE_SIZE_2M == 0,
        ensures
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn prepare_application_vmsa(
        ptr: DekoPPtr<Self>,
        vmpl2_vmsa: DekoPPtr<Self>,
        deko_ifc_handler: VirtAddr,
    ) {
        // Initializes all fields from the VMPL2 VMSA template.
        unsafe {
            core::ptr::copy(vmpl2_vmsa.addr() as *const Self, ptr.addr() as *mut Self, 1);
        }

        // We first overwrite the LSTAR field to point to the application syscall handler.
        Self::set_lstar(ptr, deko_ifc_handler.0 as u64);
    }

    /// Disables the VMSA by clearing the SVME bit in the EFER register.
    ///
    /// This function modifies the EFER (Extended Feature Enable Register) field
    /// of the VMSA to clear the SVME (Secure Virtual Machine Enable) bit (bit 12).
    /// This effectively disables the VMSA for secure execution.
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn disable(ptr: DekoPPtr<Self>) {
        unsafe {
            // 1. Get the raw pointer to the struct.
            // DO NOT convert this to &mut Self.
            let struct_ptr = ptr.addr() as *mut Self;

            // 2. Calculate the pointer to the 'rax' field specifically.
            // 'addr_of_mut!' computes the offset without creating an intermediate reference
            // to the struct, avoiding issues with unaligned/packed data or MMIO restrictions.
            let efer = core::ptr::addr_of_mut!((*struct_ptr).efer);

            // 3. Use a Volatile Write.
            // This guarantees the compiler emits a store instruction, does not optimize it away,
            // and does not try to use 'memcpy' or wide registers.
            let v = core::ptr::read_unaligned(efer) & (!(1 << 12));
            core::ptr::write_unaligned(efer, v);
        }
    }

    /// Populates the body of the guest VMSA from the parameters coming
    /// from boot arguments.
    ///
    /// This function is marked as `external_body` because we must modify
    /// the thing in place to avoid stack copy which will overflow the
    /// stack implicitly.
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(ptr_perm): Tracked<&mut DekoPointsTo<Self>>,
        requires
            old(ptr_perm).wf(),
            old(ptr_perm).is_init(),
            old(ptr_perm).pptr() == ptr@,
        ensures
            ptr_perm.wf(),
            ptr_perm.is_init(),
            ptr_perm.pptr() == ptr@,
    )]
    pub fn populate_from_igvm_params(ptr: DekoPPtr<Self>, igvm_params: &IgvmParams<'_>) {
        if let Some(guest_ctx) = igvm_params.igvm_guest_context {
            kdebug!("Guest context:", guest_ctx);

            let this = unsafe { &mut *(ptr.addr() as *mut Self) };

            // Now we populate the guest VMSA body from the guest context.
            // I'm being lazy here because no context is needed but sometimes
            // it is needed.
        } else {
            kinfo!("No guest context in IGVM detected!");
        }
    }

    /// Returns a pointer to the current VMSA.
    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(cpu_perm): Tracked<&DekoCpuCtxPermission>,
                -> vmsa_perm: Tracked<DekoPointsTo<VMSA>>,
        requires
            cpu_perm.wf_with(cpu_ctx),
        ensures
            vmsa_perm@.pptr() == r@,
            vmsa_perm@.is_init(),
            vmsa_perm@.wf(),

    )]
    pub fn this_vmsa(cpu_ctx: DekoPPtr<DekoCpuCtx>) -> DekoPPtr<VMSA> {
        unsafe {
            // Perform a dummy raed and ensure that no #PF occurs.
            let _ = &*(PERCPU_VMSA_BASE.0 as *const VMSA);
        }

        proof_with!(|= Tracked::assume_new());
        DekoPPtr(vstd::simple_pptr::PPtr(PERCPU_VMSA_BASE.0 as usize, core::marker::PhantomData))
    }
}

#[verus_verify]
impl VmsaInitialContext {
    /// Constructs a new initial VMSA context from the given RIP and CSS top.
    #[verus_spec(r =>

    )]
    pub fn new_with(rip: u64, css_top: u64, cr3: u64, tss: &X86Tss) -> Self {
        let ds = VMSASegment {
            selector: DEKO_DS,
            flags: (DEKO_DS_ATTRIBUTES & 0xff) | ((DEKO_DS_ATTRIBUTES & 0xf000) >> 4),
            limit: 0xffff_ffff,
            base: 0,
        };
        let cs = VMSASegment {
            selector: DEKO_CS,
            flags: (DEKO_CS_ATTRIBUTES & 0xff) | ((DEKO_CS_ATTRIBUTES & 0xf000) >> 4),
            limit: 0xffff_ffff,
            base: 0,
        };
        let tr = VMSASegment {
            selector: DEKO_TSS,
            flags: DEKO_TR_ATTRIBUTES,
            limit: core::mem::size_of::<X86Tss>() as u32,
            base: addr_of_ref(tss) as u64,
        };

        let (gdt_base, gdt_limit) = GLOBAL_GDT.get_base_and_limit();

        // Other APs will share the same IDT and GDT.
        let (idt_base, idt_limit) = match GLOBAL_IDT.get() {
            Some(DekoAtomicData { data: idt, perm: idt_perm }) => {
                let idt = idt.borrow(Tracked(idt_perm.borrow()));

                idt.get_base_and_limit()
            },
            None => {
                kerror!("Global IDT is not initialized");
                die("");
            },
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
            gdtr: VmsaTableRegister { _rsvd: [0;3], limit: gdt_limit, base: gdt_base },
            idtr: VmsaTableRegister { _rsvd: [0;3], limit: idt_limit, base: idt_base },
            pat: 0x0007040600070406u64,
        }
    }
}

#[verus_verify]
impl VmsaPage {
    #[inline]
    #[verus_spec(r =>
        requires
            self.wf(),
        ensures
            r.wf(),
    )]
    pub fn vaddr(&self) -> VirtAddr {
        VirtAddr::new(self.page.addr() as u64 + (self.idx as u64) * PAGE_SIZE)
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
           // Need vmsaperm.
            -> ptr_perm: Tracked<DekoPointsTo<VMSA>>,
        requires
            self.wf(),
        ensures
            r.wf(),
            ptr_perm@.pptr() == r@,
            ptr_perm@.is_init(),
            ptr_perm@.wf(),
    )]
    pub fn ptr(&self) -> DekoPPtr<VMSA> {
        proof_with!(|= Tracked::assume_new());
        DekoPPtr(vstd::simple_pptr::PPtr(self.vaddr().0 as usize, core::marker::PhantomData))
    }

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

        let (page, Tracked(perm)) = boxed_ptr!([VMSA; 2], &DEKO_FRAME_ALLOCATOR_FULL);

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
        let flags = RmpFlags::from_bits_truncate(rmp.bits() | RmpFlags::vmsa().bits());

        proof {
            assert(flags.bits() & Rmp_ALL_BITS == flags.bits()) by {
                bit_u32_and_auto();
            }
            assume(perm.is_init());
            assume(pgtable_perm.mapped(vaddr));
        }

        // Perform a RMPADJUST to set the page as VMSA.

        kdebug!("Adjusting RMP for VMSA page at vaddr:", vaddr, " with flags:", flags.bits() => hex);
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

    /// Initializes the VMSA page for guest.
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
    pub fn init_guest_vmsa(&self, reset_rip: u64) -> u64 {
        // This is similar to init_from, but only initializes the necessary fields
        // for guest VMSA.
        // SAFETY: We have the permission to the VMSA page, and we ensure that
        // the pointer is valid and properly aligned because we deref it
        // from a valid DekoPPtr.
        //
        // This prevents stack overflow. Verus does not support creating a &mut in
        // place so this requires some unsafe pointer manipulations instead.
        let this = unsafe {
            let ptr = self.page.borrow(Tracked(&perm.ptr_perm)).as_ptr().wrapping_add(
                self.idx * PAGE_SIZE as usize,
            ) as *mut VMSA;

            kdebug!("write bytes vmsa");

            core::ptr::write_bytes(ptr as *mut u8, 0, core::mem::size_of::<VMSA>());

            &mut *ptr
        };

        this.cs = real_mode_code_segment(reset_rip);
        this.ds = real_mode_data_segment();
        this.es = real_mode_data_segment();
        this.ss = real_mode_data_segment();
        this.fs = real_mode_data_segment();
        this.gs = real_mode_data_segment();
        this.gdt = real_mode_sys_seg(0);
        this.idt = real_mode_sys_seg(0);
        this.ldt = real_mode_sys_seg(0x82);  // LDT available.
        this.tr = real_mode_sys_seg(0x8b);  // 32-bit TSS available.

        this.rip = reset_rip & 0xffffu64;
        this.rflags = 0x2;
        this.cr0 = 0x60000010;
        this.vmpl = 2;
        this.dr6 = 0xffff0ff0;
        this.dr7 = 0x400;
        this.g_pat = 0x0007040600070406u64;
        this.xcr0 = 1;
        this.mxcsr = 0x1f80;
        this.x87_ftw = 0x5555;
        this.x87_fcw = 0x0040;
        this.sev_features = (SnpStatusFlags::get_status().bits() & !REST_INJ) >> 2;  // make this sev.

        this.sev_features
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
            vmpl < 4,
            old(perm).ptr_perm.wf(),
            old(perm).ptr_perm.pptr() == self.page@,
            self.wf(),
        ensures
            perm.ptr_perm.wf(),
            perm.ptr_perm.pptr() == self.page@,
            perm.ptr_perm.is_init(),
    )]
    pub fn init_from(&self, ctx: &VmsaInitialContext, vmpl: u8) -> u64 {
        // SAFETY: We have the permission to the VMSA page, and we ensure that
        // the pointer is valid and properly aligned because we deref it
        // from a valid DekoPPtr.
        let this = unsafe {
            let array_ptr = self.page.borrow(Tracked(&perm.ptr_perm)).as_ptr() as *mut VMSA;
            let target_ptr = array_ptr.add(self.idx);

            core::ptr::write_bytes(target_ptr as *mut u8, 0, core::mem::size_of::<VMSA>());

            &mut *target_ptr
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
        this.x87_fcw = 0x40;
        this.x87_ftw = 0x5555;
        this.vmpl = vmpl;
        this.vtom = 0;  // unsupported.

        if vmpl != VMPL_GUEST_DEKO_MONITOR as u8 {
            this.sev_features = (SnpStatusFlags::get_status().bits() & !REST_INJ) >> 2;
            this.tsc_aux |= VMPL1_MAGIC_KERN << 24;
        } else {
            this.sev_features = (SnpStatusFlags::get_status().bits()) >> 2;
        }

        // Being lazy
        this.sev_features
    }
}

} // verus!
