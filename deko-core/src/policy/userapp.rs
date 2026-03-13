use core::borrow::Borrow;

use deko_macros::DekoDebug;
use deko_std::address::{create_paddr_range, PhysAddr, VaddrRange};
use deko_std::bits::{bit_u32_and_auto, bit_u64_and_auto};
use deko_std::mem::PAGE_SIZE_2M;
use deko_std::misc::{early_dbg, early_die};
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::prelude::{func_ptr, VirtAddr, PAGE_SIZE, VADDR_LOWER_MASK, VADDR_UPPER_MASK};
use deko_std::ptr::{addr_of_ref, DekoPPtr};
use deko_std::std_extra::allocator::AllocatorWrapper;
use deko_std::std_extra::num::isize_abs;
use deko_std::sync::{
    DekoAtomicData, DekoRwLock, DekoSimpleOnceCell, DekoSimpleRwLock, RwLockPredicate,
};
use deko_std::wf::WellFormed;
use deko_std::{
    boxed_ptr, deko_bitflags, deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data,
    TrivialPredicate,
};
use uuid::Uuid;
use vstd::invariant;
use vstd::prelude::*;

use crate::collections::{update_vec, Vec};
use crate::cpu::gdt::{GlobalDescriptorTable, GLOBAL_GDT};
use crate::cpu::idt::GLOBAL_IDT;
use crate::cpu::ipi::wait_ipi_blocking;
use crate::cpu::irq::{log_nested_irq_state, no_irq_zone, raw_irq_enable, IrqSafeLockGuard};
use crate::cpu::regs::{no_smap_zone, DEKO_TR_ATTRIBUTES, DEKO_TSS};
use crate::cpu::task::{generate_id, DekoRunnableState};
use crate::cpu::{self, DekoCpuCtx, DekoCpuCtxPermission, X86Tss, PERCPU_AREAS};
use crate::crypto::aes::aes_gcm_256_key_gen;
use crate::crypto::uuid::{generate_secure_uuid, uuid_print};
use crate::dbg::{dump_hv_doorbell_trace_and_reset, dump_vmpl1_doorbell_snapshot_current_cpu};
use crate::guest::service::{
    DekoNewAppReq, DekoNewAppType, DEKO_SERVICE_APP_ENTER_OK, DEKO_SERVICE_APP_EXIT,
    DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER, DEKO_SERVICE_EXTEND_TIMER_EVENT,
    DEKO_SERVICE_TIMER,
};
use crate::guest::{
    guest_page_table, DekoGuestExitInformation, DekoGuestRequestParams, DekoGuestServError,
    DekoGuestServResult, DekoGuestServResultCode, DekoVmplSwitchErr, PtRegs,
    DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE,
};
use crate::imp::doorbell::{init_hv_doorbell, init_hv_doorbell_vmpl1};
use crate::imp::ghcb::{vmpl_switch, GuestHostCommunicationBlock};
use crate::imp::logging::init_ghcb_logging;
use crate::imp::vmsa::{GuestVMExit, VMSASegment};
use crate::imp::{
    flush_tlb_global_sync, RmpFlags, REST_INJ, VMPL1_MAGIC_KERN, VMPL1_MAGIC_USER,
    VMPL_GUEST_SECURE_APP,
};
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::mm::paging::{
    bit_not_in_addr_region, phys_to_virt, strip_confidentiality_bits, PageTable, PageTableEntry,
};
use crate::mm::vm::TempMapping;
use crate::mm::{
    check_within_guest_mmap, virt_to_phys, virt_to_phys_checked, DEKO_FRAME_ALLOCATOR_FULL,
};
use crate::policy::syscall::{SYS_exit, SYS_exit_group, DEKO_VMPL1_SYSCALL_TRAMPOLINE};
use crate::policy::DekoSyscallBody;
use crate::snp::ghcb::{current_ghcb, msr_register_ghcb_gpa, validate_ghcb};
use crate::snp::vmsa::{
    guest_user_code_segment, guest_user_stack_segment, VmsaPage, VmsaPagePermission, VMSA,
};
use crate::snp::{
    doorbell, init_guest_host, is_vmpl1, rmpadjust, rmpquery, VMPL_GUEST_DEKO_MONITOR,
};
use crate::{die, kdebug, kerror, kinfo, kpanic_if, kwarn, vec};

deko_bitflags! {
    pub struct DekoFile: u32 {
        const READ = 0;
        const WRITE = 1;
        const APPEND = 2;
    }
}

verus! {

/// A unique identifier for a shadowed user application running inside the guest VM.
pub type Pid = u32;

/// Application identifiers are just process ids.
pub type AppId = Pid;

/// A hashmap that keeps tracks of all shadowed user applications running inside the guest VM,
/// keyed by their Application IDs.
pub type DekoProcessMap = HashMap<AppId, DekoUserApp, DekoAllocatorApi>;

pub type DekoShimSet = HashMap<u32, (), DekoAllocatorApi>;

pub const DEKO_VMPL1_THREAD_STACK_SIZE: usize = 0x8000;

pub struct DekoShadowAppListPred;

pub struct DekoShimSetPred;

impl<P> RwLockPredicate<DekoAtomicData<Option<DekoProcessMap>, P>> for DekoShadowAppListPred {
    open spec fn inv(self, data: DekoAtomicData<Option<DekoProcessMap>, P>) -> bool {
        match data.data {
            Some(app_map) => app_map.wf(),
            None => true,
        }
    }
}

impl<P> RwLockPredicate<DekoAtomicData<Option<DekoShimSet>, P>> for DekoShimSetPred {
    open spec fn inv(self, data: DekoAtomicData<Option<DekoShimSet>, P>) -> bool {
        match data.data {
            Some(shim_set) => shim_set.wf(),
            None => true,
        }
    }
}

/// Tracks all currently running processes inside the guest VM that are spawned
/// by the container runtimes (e.g., runc, containerd) or are containerized applications.
///
/// The identifiers are the physical addresses of their main thread's CR3.
pub exec static DEKO_SHADOW_APP_LIST: DekoRwLock<
    Option<DekoProcessMap>,
    (),
    IrqSafeLockGuard,
    DekoShadowAppListPred,
>
    ensures
        DEKO_SHADOW_APP_LIST.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new(None),
        IrqSafeLockGuard {  },
        Ghost(DekoShadowAppListPred {  }),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

pub exec static DEKO_SHIM_SET: DekoRwLock<
    Option<DekoShimSet>,
    (),
    IrqSafeLockGuard,
    DekoShimSetPred,
>
    ensures
        DEKO_SHIM_SET.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new(None),
        IrqSafeLockGuard {  },
        Ghost(DekoShimSetPred {  }),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

pub exec static IS_DOCKER_RUNNING: DekoSimpleOnceCell<()>
    ensures
        IS_DOCKER_RUNNING.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub const RUNC_NAME: &'static str = "runc";

pub const CONTAINERD_NAME: &'static str = "containerd";

pub const DOCKER_INIT_NAME: &'static str = "docker-init";

pub const CONTAINERD_SHIM_NAME: &'static str = "containerd-shim";

pub const DOCKER_OVERLAY: &'static str = "overlay";

/// Checks whether the given file path is associated with Docker or container runtimes.
#[inline]
pub fn is_docker_request(path: &str) -> bool {
    path.contains(RUNC_NAME) || path.contains(CONTAINERD_NAME) || path.contains(
        CONTAINERD_SHIM_NAME,
    ) || path.contains(DOCKER_INIT_NAME) || path.contains(DOCKER_OVERLAY)
}

/// Checks whether the given parent PID belongs to a shim process.
pub fn lookup_parent_is_shim(ppid: u32) -> bool {
    deko_rwlock_read_atomic_data!(
        DEKO_SHIM_SET,
        shim_set,
        __,
        {
            match shim_set {
                Some(shim_set) => shim_set.contains_key(&ppid),
                None => false,
            }
        }
    )
}

/// Adds the given parent PID to the shim set.
pub fn add_to_shim_set(ppid: u32) {
    deko_rwlock_write_atomic_data!(
        DEKO_SHIM_SET,
        shim_set,
        __,
        {
            let mut new_shim_set = match shim_set {
                Some(set) => set,
                None => DekoShimSet::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
            };

            new_shim_set.insert(ppid, ());

            shim_set = Some(new_shim_set);
        }
    )
}

pub fn remove_from_shim_set(ppid: u32) {
    deko_rwlock_write_atomic_data!(
        DEKO_SHIM_SET,
        shim_set,
        __,
        {
            if let Some(mut set) = shim_set {
                set.remove(&ppid);
                shim_set = Some(set);
            }
        }
    )
}

#[verus_verify]
impl VmsaPage {
    /// Initializes the given VMSA page for a new user application with the provided Linux `pt_regs` context.
    ///
    /// The base VMSA comes from the VMPL2 kernel context.
    #[verus_spec(r =>
        requires
            old(vmsa).wf(),
        ensures
            vmsa.wf(),
    )]
    fn do_init_for_app(vmsa: &mut VMSA, linux_pt_regs: &PtRegs) -> DekoGuestServResult<()> {
        let DekoAtomicData { data: syscall_trampoline, .. } =
            DEKO_VMPL1_SYSCALL_TRAMPOLINE.get().ok_or(DekoGuestServError::FatalError)?;

        // Need to first get the active VMSA here.
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        proof_with!(Tracked(&cpu_perm) => Tracked(mut active_vmsa_perm));
        let active_vmsa = VMSA::this_vmsa(cpu);
        let active_vmsa_borrow = active_vmsa.borrow(Tracked(&active_vmsa_perm));

        Self::copy_from_guest_context(vmsa, active_vmsa_borrow, *syscall_trampoline);
        Self::copy_from_user_context(vmsa, linux_pt_regs);

        kdebug!("Now vmsa is ", vmsa);

        Ok(())
    }

    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            old(vmsa).wf(),
        ensures
            vmsa.wf(),
    )]
    fn do_prepare_app_resume(vmsa: &mut VMSA) {
        // We need to set the GuestVMExit code to a special value so that when the guest VM resumes and hits the first VMRUN, it will trigger a VM exit with this code, which can be used by the VMPL2 kernel to detect that the app is resuming and do some necessary preparation (e.g., setting up the shared buffer).
        // unsafe {
        //     let rflags = core::ptr::read_unaligned(core::ptr::addr_of!(vmsa.rflags));
        //     core::ptr::write_unaligned(core::ptr::addr_of_mut!(vmsa.rflags), rflags | 0x200);
        // }
    }

    #[verifier::external_body]
    #[verus_spec(
        requires
            old(vmsa_app).wf(),
            vmsa_user.is_user_regs(),
        ensures
            vmsa_app.wf(),
    )]
    fn copy_from_user_context(vmsa_app: &mut VMSA, vmsa_user: &PtRegs) {
        kdebug!("Copying from user context", vmsa_user);

        // VMPL1 GDT layout (see GlobalDescriptorTable::new_vmpl1):
        //   0x28 = user data, 0x30 = user code.
        // Selectors used in CS/SS must carry RPL=3 for user mode.
        const VMPL1_USER_DS_SEL: u16 = 0x2b;
        const VMPL1_USER_CS_SEL: u16 = 0x33;

        unsafe {
            let dst = vmsa_app as *mut VMSA;

            // Clear the general-purpose registers first
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rax), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rbx), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rcx), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rdx), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rsi), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rdi), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rbp), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r8), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r9), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r10), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r11), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r12), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r13), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r14), 0x0);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).r15), 0x0);

            // Copy the instruction pointer and stack pointer.
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rsp), vmsa_user.sp);
            // Original entry here.
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).rip), vmsa_user.bx);
            // Flags.
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*dst).rflags),
                vmsa_user.flags | 0x200,
            );

            // Make user segments explicit for VMPL1 user return path. We must
            // update the whole segment descriptors (not only selectors), otherwise
            // we may keep stale DPL=0 flags from copied kernel VMSA.
            let mut user_cs = guest_user_code_segment();
            user_cs.selector = VMPL1_USER_CS_SEL;
            let mut user_ds = guest_user_stack_segment();
            user_ds.selector = VMPL1_USER_DS_SEL;

            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).cs), user_cs);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).ss), user_ds);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).ds), user_ds);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).es), user_ds);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).fs), user_ds);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).gs), user_ds);

            // Set back the cpl.
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).cpl), 3);
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*dst).vmpl),
                VMPL_GUEST_SECURE_APP as _,
            );

            // Enable SVME.
            let efer = core::ptr::read_unaligned(core::ptr::addr_of!((*dst).efer));
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).efer), efer | (1 << 12));
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*dst).guest_exit_code),
                GuestVMExit(0),
            );

            if let Some(DekoAtomicData { data, .. }) = GLOBAL_IDT.get() {
                core::ptr::write_unaligned(
                    core::ptr::addr_of_mut!((*dst).idt.base),
                    data.addr() as _,
                );
            }
            let (this_cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
            let ext_vmpl1 = this_cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ext_vmpl1.as_ref();
            kpanic_if!(ext_vmpl1.is_none(), "Current CPU must have an extended VMPL1 context");

            let tss = &ext_vmpl1.unwrap().tss;
            let gdt = &ext_vmpl1.unwrap().gdt;
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*dst).tr),
                VMSASegment {
                    selector: 0x18,
                    flags: DEKO_TR_ATTRIBUTES,
                    limit: core::mem::size_of::<X86Tss>() as u32,
                    base: tss.addr() as u64,
                },
            );

            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).gdt.base), gdt.addr() as _);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).gdt.limit), 0x3f);
        }
    }

    #[verifier::external_body]
    #[verus_spec(
        requires
            old(vmsa_app).wf(),
            vmsa_guest_kernel.wf(),
            syscall_trampoline_base.wf(),
            syscall_trampoline_base@ >= VADDR_UPPER_MASK,
        ensures
            vmsa_app.wf(),
    )]
    fn copy_from_guest_context(
        vmsa_app: &mut VMSA,
        vmsa_guest_kernel: &VMSA,
        syscall_trampoline_base: VirtAddr,
    ) {
        const STAR_SYSCALL_CS_SHIFT: u64 = 32;
        const STAR_SYSRET_CS_SHIFT: u64 = 48;
        const STAR_CS_FIELD_MASK: u64 = 0xffff;
        const VMPL1_KERNEL_SYSCALL_CS: u64 = 0x8;

        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let id = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id;
        let syscall_trampoline_addr = syscall_trampoline_base.0.wrapping_add(
            (id as u64) * PAGE_SIZE,
        );

        unsafe {
            let src = vmsa_guest_kernel as *const VMSA;
            let dst = vmsa_app as *const VMSA as *mut VMSA;

            core::ptr::copy_nonoverlapping(src, dst, 1);
            // Patch the syscall trampoline address.
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*dst).lstar),
                syscall_trampoline_addr,
            );

            // Keep SYSRET selectors from the guest but force SYSCALL kernel CS to
            // the VMPL1 GDT kernel code selector (0x8). Otherwise SYSCALL enters
            // with CS=0x10 (Linux layout), which conflicts with our VMPL1 GDT and
            // can make #HV postpone iretq fail with #GP(selector=0x10).
            let old_star = core::ptr::read_unaligned(core::ptr::addr_of!((*dst).star));
            let sysret_cs = (old_star >> STAR_SYSRET_CS_SHIFT) & STAR_CS_FIELD_MASK;
            let new_star = (sysret_cs << STAR_SYSRET_CS_SHIFT) | (VMPL1_KERNEL_SYSCALL_CS
                << STAR_SYSCALL_CS_SHIFT);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).star), new_star);

            core::ptr::write_bytes(core::ptr::addr_of_mut!((*dst).intercept_vecs), 0, 0x20);
            core::ptr::write_bytes(core::ptr::addr_of_mut!((*dst).intercept_msr_vecs), 0, 0x20);

            // Write special magic to the TSC_AUX.
            let tsc_aux = core::ptr::read_unaligned(core::ptr::addr_of!((*dst).tsc_aux));
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!((*dst).tsc_aux),
                tsc_aux | (VMPL1_MAGIC_USER << 24),
            );

            // Enable REST_INJ.
            let mut sev_features = core::ptr::read_unaligned(
                core::ptr::addr_of!((*dst).sev_features),
            );
            sev_features |= (REST_INJ >> 2);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!((*dst).sev_features), sev_features);
        }
    }

    /// Prepare the user context for VMPL1 so that the caller can kick the current vCPU
    /// into the desired user application with this VMSA.
    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(vmsa_page_perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(self).wf(),
            old(vmsa_page_perm).ptr_perm.wf(),
            old(vmsa_page_perm).ptr_perm.is_init(),
            old(vmsa_page_perm).ptr_perm.pptr() == old(self).page@,
            linux_pt_regs.is_user_regs(),
        ensures
            self.wf(),
            vmsa_page_perm.ptr_perm.wf(),
            vmsa_page_perm.ptr_perm.is_init(),
            vmsa_page_perm.ptr_perm.pptr() == self.page@,
    )]
    pub fn init_for_app(&mut self, linux_pt_regs: &PtRegs) -> DekoGuestServResult<()> {
        let vmsa = &mut unsafe { &mut *(self.page.addr() as *mut [VMSA; 2]) }[self.idx as usize];

        Self::do_init_for_app(vmsa, linux_pt_regs)
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(vmsa_page_perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(self).wf(),
            old(vmsa_page_perm).ptr_perm.wf(),
            old(vmsa_page_perm).ptr_perm.is_init(),
            old(vmsa_page_perm).ptr_perm.pptr() == old(self).page@,
        ensures
            self.wf(),
            vmsa_page_perm.ptr_perm.wf(),
            vmsa_page_perm.ptr_perm.is_init(),
            vmsa_page_perm.ptr_perm.pptr() == self.page@,
    )]
    pub fn prepare_app_resume(&mut self) {
        let vmsa = &mut unsafe { &mut *(self.page.addr() as *mut [VMSA; 2]) }[self.idx as usize];

        Self::do_prepare_app_resume(vmsa);
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(vmsa_page_perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(self).wf(),
            old(vmsa_page_perm).ptr_perm.wf(),
            old(vmsa_page_perm).ptr_perm.is_init(),
            old(vmsa_page_perm).ptr_perm.pptr() == old(self).page@,
        ensures
            self.wf(),
            vmsa_page_perm.ptr_perm.wf(),
            vmsa_page_perm.ptr_perm.is_init(),
            vmsa_page_perm.ptr_perm.pptr() == self.page@,
    )]
    pub fn enable_svme(&mut self) {
        let vmsa = &mut unsafe { &mut *(self.page.addr() as *mut [VMSA; 2]) }[self.idx as usize];
        let efer = core::ptr::addr_of_mut!(vmsa.efer);

        unsafe {
            let val = core::ptr::read_unaligned(efer) | (1 << 12);
            core::ptr::write_unaligned(efer, val);
        }
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(vmsa_page_perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(self).wf(),
            old(vmsa_page_perm).ptr_perm.wf(),
            old(vmsa_page_perm).ptr_perm.is_init(),
            old(vmsa_page_perm).ptr_perm.pptr() == old(self).page@,
        ensures
            self.wf(),
            vmsa_page_perm.ptr_perm.wf(),
            vmsa_page_perm.ptr_perm.is_init(),
            vmsa_page_perm.ptr_perm.pptr() == self.page@,
    )]
    pub fn set_thread_bases(&mut self, fs_base: u64, gs_base: u64, kernel_gs_base: u64) {
        let vmsa = &mut unsafe { &mut *(self.page.addr() as *mut [VMSA; 2]) }[self.idx as usize];

        unsafe {
            core::ptr::write_unaligned(core::ptr::addr_of_mut!(vmsa.fs.base), fs_base);
            core::ptr::write_unaligned(core::ptr::addr_of_mut!(vmsa.gs.base), gs_base);
            core::ptr::write_unaligned(
                core::ptr::addr_of_mut!(vmsa.kernel_gs_base),
                kernel_gs_base,
            );
        }
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(vmsa_page_perm): Tracked<&VmsaPagePermission>,
        requires
            self.wf(),
            vmsa_page_perm.ptr_perm.wf(),
            vmsa_page_perm.ptr_perm.is_init(),
            vmsa_page_perm.ptr_perm.pptr() == self.page@,
        ensures
            r.wf(),
    )]
    pub fn snapshot(&self) -> VMSA {
        unsafe { core::ptr::read(self.vaddr().0 as *const VMSA) }
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        with
            Tracked(vmsa_page_perm): Tracked<&mut VmsaPagePermission>,
        requires
            old(self).wf(),
            snapshot.wf(),
            old(vmsa_page_perm).ptr_perm.wf(),
            old(vmsa_page_perm).ptr_perm.is_init(),
            old(vmsa_page_perm).ptr_perm.pptr() == old(self).page@,
        ensures
            self.wf(),
            vmsa_page_perm.ptr_perm.wf(),
            vmsa_page_perm.ptr_perm.is_init(),
            vmsa_page_perm.ptr_perm.pptr() == self.page@,
    )]
    pub fn restore_from_snapshot(&mut self, snapshot: &VMSA) {
        unsafe {
            core::ptr::copy_nonoverlapping(snapshot as *const VMSA, self.vaddr().0 as *mut VMSA, 1);
        }
    }
}

/// A regular file opened by a shadowed user application.
#[derive(DekoDebug)]
pub struct DekoUserFile {
    /// The path to the file.
    pub path: [u8; 256],
    /// The flags associated with the file (read, write, append).
    pub flags: DekoFileFlags,
    /// The current offset in the file; if minus, counts from the end of the file.
    pub offset: isize,
    /// The size of the file.
    pub size: usize,
}

impl WellFormed for DekoUserFile {
    open spec fn wf(&self) -> bool {
        &&& self.flags.wf()
        &&& self.flags.bits() & DekoFile_ALL_BITS == self.flags.bits()
        &&& isize_abs(self.offset as int) as usize <= self.size
    }
}

/// The resources associated with a shadowed user application running inside the guest VM.
/// These can be file descriptors, memory mappings, etc.
#[derive(DekoDebug)]
pub enum DekoUserAppResource {
    /// A regular file.
    File(DekoUserFile),
    /// A network socket.
    Socket,
}

impl WellFormed for DekoUserAppResource {
    open spec fn wf(&self) -> bool {
        match self {
            DekoUserAppResource::File(f) => f.wf(),
            DekoUserAppResource::Socket => true,
        }
    }
}

#[repr(u8)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoUserAppState {
    /// The application is currently running inside the guest VM.
    Running = 0,
    /// The application has exited but has not been reaped by the guest kernel yet.
    Created,
    /// The application has exited and has been reaped by the guest kernel.
    Exit,
}

impl WellFormed for DekoUserAppState {
    open spec fn wf(&self) -> bool {
        true
    }
}

#[repr(u8)]
#[derive(DekoDebug, Clone, Copy, PartialEq, Eq)]
pub enum DekoUserAppMigrationState {
    /// No migration is currently in progress for this task.
    Idle = 0,
    /// A synchronous handoff is in progress.
    Migrating,
}

impl WellFormed for DekoUserAppMigrationState {
    open spec fn wf(&self) -> bool {
        true
    }
}

/// Thread-private VMPL1 state owned by the Linux task.
#[derive(DekoDebug)]
pub struct DekoUserThread {
    pub tid: u32,
    pub kernel_vmpl1_stack_base: VirtAddr,
    pub kernel_vmpl1_stack_top: VirtAddr,
    pub kernel_vmpl1_rsp: u64,
    pub fs_base: u64,
    pub gs_base: u64,
    pub kernel_gs_base: u64,
}

impl WellFormed for DekoUserThread {
    open spec fn wf(&self) -> bool {
        &&& self.kernel_vmpl1_stack_base.wf()
        &&& self.kernel_vmpl1_stack_top.wf()
        &&& self.kernel_vmpl1_stack_base@ < self.kernel_vmpl1_stack_top@
        &&& self.kernel_vmpl1_stack_top@ - self.kernel_vmpl1_stack_base@
            == DEKO_VMPL1_THREAD_STACK_SIZE as u64
        &&& self.kernel_vmpl1_rsp >= self.kernel_vmpl1_stack_base@
        &&& self.kernel_vmpl1_rsp <= self.kernel_vmpl1_stack_top@
        &&& self.kernel_vmpl1_rsp % 16 == 0
    }
}

/// The type of the shadowed user application.
#[derive(DekoDebug)]
pub struct DekoUserAppExt {
    /// Opened resources associated with this user application.
    ///
    /// These are typically file descriptors mapped to files or sockets.
    pub opened_files: HashMap<u64, DekoUserAppResource, DekoAllocatorApi>,
    /// The AES-GCM-256 key used for transparently encrypting/decrypting
    /// this user application's data if (label  ̸⊆ label_public).
    pub key: [u8; 32],
    /// Occupied memory regions by this user application.
    pub occupied_regions: Vec<VaddrRange>,
    /// Sha3-384 measurement of the user application's binary.
    pub measurement: [u8; 48],
    /// The current state of this user application.
    pub state: DekoUserAppState,
    /// Which CPU currently owns the authoritative VMPL1 shadow state.
    pub owner_cpu: u32,
    /// Which CPU currently has this task loaded in its VMPL1 runtime slot.
    pub loaded_cpu: Option<u32>,
    /// Monotonic counter bumped on each completed shadow-state handoff.
    pub state_version: u64,
    /// Migration state for synchronous cross-core handoff.
    pub migration_state: DekoUserAppMigrationState,
    /// Saved VMPL1 VMSA snapshot for cross-core resume.
    pub saved_vmsa: Option<VMSA>,
    /// The shared buffer between the application and the VMPL2 kernel.
    pub shared_buf: DekoSimpleOnceCell<VirtAddr>,
}

impl WellFormed for DekoUserAppExt {
    open spec fn wf(&self) -> bool {
        &&& forall|fd: u64|
            #![trigger self.opened_files@[fd]]
            self.opened_files@.contains_key(fd) ==> self.opened_files@[fd].wf()
        &&& forall|i: int|
            #![trigger self.occupied_regions@[i]]
            0 <= i < self.occupied_regions.len() ==> {
                &&& self.occupied_regions@[i].wf()
                &&& self.occupied_regions@[i].start@ % PAGE_SIZE == 0
                &&& self.occupied_regions@[i].end@
                    <= 0x8000_0000_0000  // Linux user-space limit

            }&&& self.measurement.len() == 48
        &&& self.state.wf()
        &&& self.migration_state.wf()
        &&& self.saved_vmsa is Some ==> self.saved_vmsa.unwrap().wf()
        &&& self.shared_buf.wf()
    }
}

/// A shadowed user application (mimicking task_struct) running inside the guest VM.
///
/// This structure bridges the gap between hardware reality (CR3) and
/// Linux logical abstraction (PID, Comm, Namespaces).
#[derive(DekoDebug)]
pub struct DekoUserApp {
    /// The Page Table Base Address (CR3).
    /// In a non-KPTI environment, this is the ultimate, spoof-proof identifier
    /// for the memory context of this application.
    /// Maps to: CPU register CR3 / task_struct->mm->pgd
    pub cr3: PhysAddr,
    /// The Process ID seen by the Guest Kernel.
    /// Essential for correlating with sys_wait4, logs, and user tools.
    /// Maps to: task_struct->pid
    pub pid: u32,
    /// The Thread Group ID.
    /// Essential for handling `sys_exit_group` (kill all threads).
    /// If tgid == pid, this is the main thread.
    /// Maps to: task_struct->tgid
    pub tgid: u32,
    /// The Parent's PID.
    /// Used to reconstruct the process tree.
    /// E.g., Identify if this process was spawned by `runc` or `containerd`.
    /// Maps to: task_struct->real_parent->pid
    pub parent_pid: u32,
    /// Container ID / Namespace Hash.
    /// If you track namespaces, this identifies the "Sandbox".
    /// 0 usually means Host Namespace.
    /// Maps to: Hash of (task_struct->nsproxy->mnt_ns)
    #[deko(hex)]
    pub container_id: u64,
    /// User ID (Effective UID).
    /// Used for basic privilege checks (is this root?).
    /// Maps to: task_struct->cred->euid
    pub uid: u32,
    /// Per-thread VMPL1 kernel state for the main thread.
    pub thread: DekoUserThread,
    // Deko Security Extensions.
    pub ext: DekoUserAppExt,
}

impl WellFormed for DekoUserApp {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.cr3@ % PAGE_SIZE == 0
        &&& self.cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64
        &&& self.cr3.wf()
        &&& self.thread.wf()
        &&& self.ext.wf()
    }
}

#[verus_verify]
impl DekoUserApp {
    /// Binds this user application to the given CPU for local run, and initializes
    /// the shared buffer if provided.
    #[verifier::external_body]
    fn bind_for_local_run(&mut self, cpu_id: u32, shared_buf: Option<VirtAddr>) {
        self.ext.state = DekoUserAppState::Running;
        self.ext.owner_cpu = cpu_id;
        self.ext.loaded_cpu = Some(cpu_id);
        self.ext.migration_state = DekoUserAppMigrationState::Idle;

        if let Some(buf) = shared_buf {
            self.ext.shared_buf.init(buf);
        }
    }

    /// Stage 1 CPU migration from the old CPU to the current CPU: mark the migration
    /// in *progress* and update the owner and loaded CPU fields.
    #[verifier::external_body]
    fn mark_fake_handoff_in_progress(&mut self, old_cpu: u32) -> u64 {
        self.ext.owner_cpu = old_cpu;
        self.ext.loaded_cpu = Some(old_cpu);
        self.ext.migration_state = DekoUserAppMigrationState::Migrating;
        self.ext.state_version = self.ext.state_version.wrapping_add(1);
        self.ext.state_version
    }

    #[verifier::external_body]
    #[verus_spec(
        requires
            old(self).wf(),
            vmsa.wf(),
        ensures
            self.wf(),
            vmsa.wf(),
    )]
    fn save_vmsa_snapshot(&mut self, vmsa: &VMSA) {
        self.ext.saved_vmsa = Some(unsafe { core::ptr::read(vmsa as *const VMSA) });
    }

    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            vmsa.wf(),
        ensures
            vmsa.wf(),
            r.wf(),
    )]
    fn copy_vmsa_snapshot(vmsa: &VMSA) -> VMSA {
        unsafe { core::ptr::read(vmsa as *const VMSA) }
    }

    /// Creates a new [`DekoUserApp`] with a unique id, an empty set of opened files,
    /// and a randomly generated AES-GCM-256 key.
    #[verifier::external_body]
    #[verus_spec(r =>
        requires
            app_req.wf(),
            guest_cr3.wf(),
            guest_cr3@ % PAGE_SIZE == 0,
            guest_cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64,
            app_req.start_code@ > 0,
            app_req.start_code@ % PAGE_SIZE == 0,
            app_req.start_code@ < app_req.end_code@,
            app_req.end_code@ <= VADDR_LOWER_MASK, // Linux user-space limit
        ensures
            r matches Ok(r) ==> r.wf(),
    )]
    pub fn new(app_req: &DekoNewAppReq, guest_cr3: PhysAddr) -> DekoGuestServResult<Self> {
        kinfo!("Creating new DekoUserApp with request", app_req, guest_cr3=>hex);

        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let owner_cpu = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id as u32;
        let (vmpl1_stack_ptr, _) =
            boxed_ptr!([u8; DEKO_VMPL1_THREAD_STACK_SIZE], &DEKO_FRAME_ALLOCATOR_FULL);
        let kernel_vmpl1_stack_base = vmpl1_stack_ptr.into_vaddr();
        let kernel_vmpl1_stack_top = VirtAddr(
            kernel_vmpl1_stack_base.0.wrapping_add(DEKO_VMPL1_THREAD_STACK_SIZE as u64),
        );

        let start_code = VirtAddr(app_req.start_code);
        let end_code = VirtAddr(app_req.end_code);
        let range = start_code..end_code;

        let mut r = Self {
            pid: app_req.pid,
            tgid: app_req.tgid,
            parent_pid: app_req.ppid,
            uid: app_req.uid,
            container_id: app_req.mnt_ns_id,
            cr3: guest_cr3,
            thread: DekoUserThread {
                tid: app_req.pid,
                kernel_vmpl1_stack_base,
                kernel_vmpl1_stack_top,
                kernel_vmpl1_rsp: kernel_vmpl1_stack_top.0,
                fs_base: app_req.fs_base,
                gs_base: app_req.gs_base,
                kernel_gs_base: app_req.kernel_gs_base,
            },
            ext: DekoUserAppExt {
                opened_files: HashMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
                key: {
                    let mut key = [0u8;32];
                    aes_gcm_256_key_gen(&mut key);
                    key
                },
                occupied_regions: vec![],
                measurement: [0u8;48],
                state: DekoUserAppState::Created,
                owner_cpu,
                loaded_cpu: None,
                state_version: 0,
                migration_state: DekoUserAppMigrationState::Idle,
                saved_vmsa: None,
                shared_buf: DekoSimpleOnceCell::new(Ghost(())),
            },
        };

        // TODO: Add this.
        // r.add_and_measure(range)?;

        // Finally, mark the memory regions owned by this application not visible to
        // VMPL2 by lifting the VMPL to VMPL1 in the RMP table.
        r.lift_vmpl()?;

        Ok(r)
    }

    /// Adds this memory region to the list of occupied regions
    /// and updates the measurement of the user application.
    #[verus_spec(r =>
        requires
            old(self).wf(),
            region.wf(),
            region.start@ > 0,
            region.start@ % PAGE_SIZE == 0,
            region.end@ <= VADDR_LOWER_MASK, // Linux user-space limit
        ensures
            self.wf(),
    )]
    pub fn add_and_measure(&mut self, region: VaddrRange) -> DekoGuestServResult<()> {
        let len = (region.end.0 - region.start.0 + PAGE_SIZE - 1) / PAGE_SIZE;
        let mut i = 0;
        let mut buf = vec![0u8; (PAGE_SIZE + 48) as usize];

        // Copy the hash to the buffer first.
        for j in 0..48
            invariant
                buf@.len() == (PAGE_SIZE + 48) as int,
                self.ext.measurement@.len() == 48,
                self.wf(),
        {
            update_vec(&mut buf, j, self.ext.measurement[j]);
        }

        #[verus_spec(
            invariant
                i <= len,
                buf@.len() == (PAGE_SIZE + 48) as int,
                len == (region.end@ - region.start@ + PAGE_SIZE - 1) / PAGE_SIZE as int,
                region.start@ > 0,
                region.end@ <= VADDR_LOWER_MASK,
                region.start@ % PAGE_SIZE == 0,
                PAGE_SIZE == 0x1000,
                VADDR_LOWER_MASK == 0x0000_7FFF_FFFF_FFFF,
                self.wf(),
            decreases
                len - i,
        )]
        while i < len {
            let cur = VirtAddr(region.start.0 + i * PAGE_SIZE);
            let remaining_bytes = region.end.0 - cur.0;
            let bytes_to_read = PAGE_SIZE.min(remaining_bytes) as usize;
            unsafe {
                copy_from_user(self.cr3, cur, buf.as_mut_ptr().add(48), bytes_to_read)?;
            }

            kdebug!("Reading page", cur=>hex, bytes_to_read=>hex);
            kdebug!("Content is:", buf);

            if bytes_to_read < PAGE_SIZE as usize {
                for k in bytes_to_read..(PAGE_SIZE as usize)
                    invariant
                        buf@.len() == (PAGE_SIZE + 48) as int,
                {
                    update_vec(&mut buf, 48 + k, 0);
                }
            }
            // Then we measure this page.
            //
            // This is a demo for now so the order does not matter and we
            // only care about the potential performance implications.
            //
            // For production-ready systems, we should consider using a Merkle tree
            // or other authenticated data structures to efficiently and securely
            // manage the measurements.

            let hash = crate::crypto::hash::sha3_384_hash(&buf);
            for j in 0..48
                invariant
                    buf@.len() == (PAGE_SIZE + 48) as int,
                    hash@.len() == 48,
                    self.wf(),
            {
                let b = hash[j];
                update_vec(&mut buf, j, b);
                self.ext.measurement[j] = b;
            }

            kdebug!("Measured page", cur=>hex, hash);

            i += 1;
        }

        self.ext.occupied_regions.push(region.clone());

        Ok(())
    }

    /// Lifts the VMPL of the application's memory space to VMPL1.
    ///
    /// The default VMPL is the same as the guest kernel (VMPL2) but whenever there is
    /// a sensitive operation that receives the user's sensitive data (e.g., read from
    /// an encrypted socket), we need to lift the VMPL to VMPL1 to prevent the untrusted
    /// kernel from snooping on the data.
    ///
    /// This function does the thing by walking the page tables and updating the VMPL bits
    /// such that VMPL2 no longer has the read/write/execution permissions.
    #[verus_spec(r =>
        requires
            self.wf(),
    )]
    pub fn lift_vmpl(&self) -> DekoGuestServResult<()> {
        let cr3 = PageTable::map_guest_cr3(self.cr3)?;
        let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
        let private_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).private_bit;
        let shared_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).shared_bit;

        let s = self.ext.occupied_regions.len();
        for i in 0..s
            invariant
                s == self.ext.occupied_regions@.len(),
                self.wf(),
                cr3.wf(),
                cr3.inner.end@ - cr3.inner.start@ == PAGE_SIZE,
        {
            let cur = &self.ext.occupied_regions[i];
            let start = cur.start;
            let end = cur.end;
            let len = (end.0 - start.0 + PAGE_SIZE - 1) / PAGE_SIZE;
            let mut j = 0;

            #[verus_spec(
                invariant
                    j <= len,
                    cur == self.ext.occupied_regions@[i as int],
                    len == (end@ - start@ + PAGE_SIZE - 1) / PAGE_SIZE as int,
                    self.wf(),
                    cr3.wf(),
                    cr3.inner.end@ - cr3.inner.start@ == PAGE_SIZE,
                    PAGE_SIZE == 0x1000,
                decreases
                    len - j,
            )]
            while j < len {
                broadcast use RmpFlags::lemma_each_bit_is_valid;

                proof {
                    bit_u32_and_auto();
                    bit_u64_and_auto();
                }

                let va = VirtAddr(start.0 + j * PAGE_SIZE);
                // Look up the mapping.
                let mapping = PageTable::walk_lvl3_guest(&cr3, va, private_bit, shared_bit)?;
                if mapping.temp_mappings.len() <= 2 || mapping.temp_mappings.len() > 4 {
                    return Err(
                        DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
                    );
                }
                let final_mapping = mapping.final_mapping().unwrap();

                let (_, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
                assume(cpu_perm.pgtable_perm.mapped(final_mapping.inner.start));

                // First we will need to revoke the access permission for VMPL2.
                // if rmpadjust(
                //     final_mapping.inner.start,
                //     PAGE_SIZE,
                //     RmpFlags::revoke_guest_vmpl2(),
                //     Tracked(&mut cpu_perm.pgtable_perm),
                // ) != 0 {
                //     kerror!("Failed to adjust RMP for revoking VMPL2", final_mapping.inner.start=>hex);
                //     return Err(
                //         DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
                //     );
                // }
                // if rmpadjust(
                //     final_mapping.inner.start,
                //     PAGE_SIZE,
                //     RmpFlags::rwx_guest_vmpl1(),
                //     Tracked(&mut cpu_perm.pgtable_perm),
                // ) != 0 {
                //     kerror!("Failed to adjust RMP for lifting VMPL", final_mapping.inner.start=>hex);
                //     return Err(
                //         DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
                //     );
                // }
                flush_tlb_global_sync();

                kinfo!("Lifted VMPL for guest page", (start.0 + j * PAGE_SIZE) => hex);
                j += 1;
            }

        }

        Ok(())
    }
}

/// Copies data from a user application's memory space into the our memory space.
///
/// This function should be called if our `cr3` is not the same as the guest's `cr3`;
/// so we need to manually walk the guest page tables to read the data.
#[verus_spec(r =>
    requires
        0 < from@,
        guest_cr3.wf(),
        guest_cr3@ % PAGE_SIZE == 0,
        guest_cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64,
        from@ + len <= 0x8000_0000_0000,
)]
pub(crate) fn copy_from_user(
    guest_cr3: PhysAddr,
    from: VirtAddr,
    buf: *mut u8,
    len: usize,
) -> DekoGuestServResult<usize> {
    let offset_4k = from.0 & 0xfff;
    let offset_2m = from.0 & 0x1fffff;
    let from = VirtAddr(from.0 & (!0xfff));

    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let private_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).private_bit;
    let shared_bit = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).shared_bit;
    let guest_cr3_p = strip_confidentiality_bits(guest_cr3.0, private_bit);

    proof {
        let cr3 = guest_cr3@;
        assert(guest_cr3_p <= cr3 && guest_cr3_p % PAGE_SIZE == 0) by (bit_vector)
            requires
                guest_cr3_p == cr3 & !(private_bit as u64),
                bit_not_in_addr_region(private_bit),
                cr3 % PAGE_SIZE == 0,
        ;
    }

    let guest_cr3 = TempMapping::new(create_paddr_range(PhysAddr(guest_cr3_p), 1)).ok_or(
        DekoGuestServError::SoftError(DekoGuestServResultCode::Busy),
    )?;

    let mapping = PageTable::walk_lvl3_guest(&guest_cr3, from, private_bit, shared_bit)?;
    if mapping.temp_mappings.len() <= 2 || mapping.temp_mappings.len() > 4 {
        kinfo!(
            "copy_from_user: unexpected number of temp mappings",
            mapping.temp_mappings.len()
        );
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let final_mapping = mapping.final_mapping().unwrap();
    let offset = if mapping.lvl == 0 {
        offset_4k
    } else {
        offset_2m
    };

    let addr = final_mapping.inner.start.0.wrapping_add(offset);

    // Pre-filter the length to avoid overflow.
    //
    // The guest will always prepare the argument in a way such that it will
    // never cross the mapping boundary (i.e., page boundary).
    let len = len.min(final_mapping.inner.end.0.wrapping_sub(addr) as usize);

    // SAFETY: We have established a temporary mapping to the user application's
    // memory space; so we can safely read from it.
    unsafe { copy_from_user_same_vmpl((final_mapping.inner.start.0.wrapping_add(offset)), buf, len)
    }
}

/// Different from [`copy_from_user`], this function lives within the same VMPL and
/// the same `cr3` as the user application; so we can directly read from the user
/// application's memory space with SMAP disabled.
///
/// Pointers are Linux cacnonical user-space addresses.
#[verus_spec(r =>
)]
#[inline(always)]
#[verifier::external_body]
unsafe fn copy_from_user_same_vmpl(addr: u64, buf: *mut u8, len: usize) -> DekoGuestServResult<
    usize,
> {
    kdebug!("copy_from_user_same_vmpl", addr =>hex, buf as u64 =>hex, len);

    no_smap_zone(
        ||
            {
                let src_ptr = addr as *const u8;
                let dst_ptr = buf;
                core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, len);
            },
    );

    Ok(len)
}

/// Registers a new shadowed user application inside the guest VM.
///
/// The user applications can be either the container runtimes (e.g., runc, containerd)
/// or the actual containerized applications (e.g., nginx, redis). They are differentiated
/// via their namespace ids.
#[verus_spec(r =>
    requires
        guest_cr3.wf(),
)]
pub fn register_user_app(
    req: &mut DekoNewAppReq,
    guest_cr3: PhysAddr,
    is_creation: bool,
) -> DekoGuestServResult<()> {
    // Check if the cr3 is valid in the current context.
    if core::hint::unlikely(!check_within_guest_mmap(guest_cr3) || guest_cr3.0 % PAGE_SIZE != 0) {
        kerror!("register_user_app: invalid guest CR3", guest_cr3);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let comm = req.comm;
    let comm = core::ffi::CStr::from_bytes_until_nul(&comm).map_err(
        |_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
    )?.to_str().map_err(|_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))?;

    if is_creation {
        do_reigster_user_app(req, comm, guest_cr3)
    } else {
        Ok(())
    }
}

#[inline]
#[verus_spec(r =>
    ensures
        r == (req.start_code > 0 &&
            req.start_code % PAGE_SIZE == 0 &&
            req.start_code < req.end_code &&
            req.end_code <= VADDR_LOWER_MASK),
)]
fn check_user_vrange(req: &DekoNewAppReq) -> bool {
    req.start_code > 0 && req.start_code % PAGE_SIZE == 0 && req.start_code < req.end_code
        && req.end_code <= VADDR_LOWER_MASK
}

#[verus_spec(r =>
    requires
        guest_cr3.wf(),
        guest_cr3@ % PAGE_SIZE == 0,
)]
fn do_reigster_user_app(
    req: &mut DekoNewAppReq,
    comm: &str,
    guest_cr3: PhysAddr,
) -> DekoGuestServResult<()> {
    if core::hint::unlikely(
        guest_cr3.0 % PAGE_SIZE != 0 || guest_cr3.0 >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE,
    ) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    match req.app_type {
        DekoNewAppType::DEKO_DOCKER_INFRA => {
            add_to_shim_set(req.pid);

            Ok(())
        },
        DekoNewAppType::DEKO_DOCKER_APPS => {
            // Look up if the parent is a shim process.
            if !lookup_parent_is_shim(req.ppid) {
                // Ignore.
                return Ok(());
            }
            if core::hint::unlikely(!check_user_vrange(req)) {
                kerror!("do_register_user_app: invalid user vaddr range", comm, req.start_code=>hex, req.end_code=>hex);
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
            let user_app = DekoUserApp::new(req, guest_cr3)?;
            req.kernel_vmpl1_rsp = user_app.thread.kernel_vmpl1_rsp;

            deko_rwlock_write_atomic_data! {
                DEKO_SHADOW_APP_LIST,
                app_list,
                __,
                {
                    let mut napp_list = match app_list {
                        Some(mut ap) => ap,
                        None => DekoProcessMap::new_in(AllocatorWrapper(DekoAllocatorApi {  })),
                    };
                    let ghost old_napp_list = napp_list@;

                    napp_list.insert(req.tgid, user_app);

                    proof {
                        assert(napp_list@ =~= old_napp_list.insert(req.tgid, user_app));
                        assert(napp_list.wf());
                    }

                    app_list = Some(napp_list);
                }
            }

            Ok(())
        },
        _ => Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam)),
    }
}

/// Try to kick the applications in the guest VM to VMPL1.
#[verus_spec(
    requires
        // syscall_buf_mapping.wf(),
        // syscall_buf_mapping.inner.start@ + syscall_buf_offset as u64 +
        //     core::mem::size_of::<DekoSyscallBody>() as u64 <= syscall_buf_mapping.inner.end@,
)]
#[verifier::exec_allows_no_decreases_clause]
pub fn try_kick_app(
    regs: &PtRegs,
    guest_cr3: PhysAddr,
    pid: u32,
    shared_buf: VirtAddr,
    ret_params: &mut DekoGuestRequestParams,
) -> DekoGuestServResult<u64> {
    let (cpu_ptr, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    if core::hint::unlikely(cpu_ptr.borrow(Tracked(&cpu_perm.ptr_perm)).ext_vmpl1.is_none()) {
        kerror!("try_kick_app: no VMPL1 context allocated for this CPU");
        return Err(DekoGuestServError::FatalError);
    }
    // Look up the user application hashmap and see the current status
    // of the application to decide whether this is an initial launch
    // or a resume.

    let app_status =
        deko_rwlock_write_atomic_data!(
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(mut napp_list) = app_list {
                // Need to check and update the application's status.
                if !napp_list.contains_key(&pid) {
                    app_list = Some(napp_list);

                    kerror!("try_kick_app: no shadowed application found for pid", pid);
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
                    let old_state = napp_list.get(&pid).as_ref().unwrap().ext.state;
                    match old_state {
                        DekoUserAppState::Created => {
                            let mut app = napp_list.remove(&pid).unwrap();
                            let current_cpu = cpu_ptr.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id as u32;
                            app.bind_for_local_run(current_cpu, Some(shared_buf));
                            napp_list.insert(pid, app);
                            app_list = Some(napp_list);

                            proof {
                                // TODO.
                                assert(napp_list.wf()) by {
                                    admit();
                                }
                            }

                            Ok(old_state)
                        },
                        DekoUserAppState::Exit => {
                            app_list = Some(napp_list);

                            kerror!("try_kick_app: application has already exited for pid", pid);
                            Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                        },
                        DekoUserAppState::Running => {
                            app_list = Some(napp_list);

                            Ok(old_state)
                        },
                    }
                }
            } else {
                kerror!("try_kick_app: no shadowed applications found for pid", pid);

                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
            }
        }
    )?;

    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    if core::hint::unlikely(cpu_borrow.ext_vmpl1.is_none()) {
        kerror!("try_kick_app: no VMPL1 context allocated for this CPU");
        return Err(DekoGuestServError::FatalError);
    }
    let mut cpu_taken = cpu.take(Tracked(&mut cpu_perm.ptr_perm));
    let mut ctx_vmpl1 = cpu_taken.ext_vmpl1.take().unwrap();

    let tracked mut vmpl1_perm = cpu_perm.ext_vmpl1_perm.tracked_take();
    let created_thread_bases = match app_status {
        DekoUserAppState::Created => deko_rwlock_read_atomic_data! {
            DEKO_SHADOW_APP_LIST,
            app_list,
            __,
            {
                if let Some(app_list_inner) = app_list {
                    if let Some(app) = app_list_inner.get(&pid) {
                        Ok((app.thread.fs_base, app.thread.gs_base, app.thread.kernel_gs_base))
                    } else {
                        Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                    }
                } else {
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                }
            }
        }?,
        _ => (0, 0, 0),
    };

    match app_status {
        DekoUserAppState::Created => {
            proof_with!(Tracked(&mut vmpl1_perm.vmsa_perm));
            ctx_vmpl1.vmsa.init_for_app(regs)?;
            proof_with!(Tracked(&mut vmpl1_perm.vmsa_perm));
            ctx_vmpl1.vmsa.set_thread_bases(
                created_thread_bases.0,
                created_thread_bases.1,
                created_thread_bases.2,
            );
        },
        DekoUserAppState::Running => {
            proof_with!(Tracked(&mut vmpl1_perm.vmsa_perm));
            ctx_vmpl1.vmsa.prepare_app_resume();
        },
        _ => return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam)),
    }

    proof_with!(Tracked(&mut vmpl1_perm.vmsa_perm));
    ctx_vmpl1.vmsa.enable_svme();

    proof {
        cpu_perm.ext_vmpl1_perm = Some(vmpl1_perm);
    }
    cpu_taken.ext_vmpl1 = Some(ctx_vmpl1);
    cpu.write(Tracked(&mut cpu_perm.ptr_perm), cpu_taken);
    bind_current_cpu_vmpl1_slot(cpu, Tracked(&mut cpu_perm), pid);

    proof_with!(Tracked(&mut cpu_perm));
    run_userapp(cpu, ret_params)
}

pub(crate) fn bind_current_cpu_vmpl1_slot(
    cpu_ptr: DekoPPtr<DekoCpuCtx>,
    Tracked(cpu_perm0): Tracked<&mut DekoCpuCtxPermission>,
    pid: u32,
)
    requires
        old(cpu_perm0).wf_with(cpu_ptr),
        old(cpu_perm0).ptr_perm.value().ext_vmpl1 is Some,
    ensures
        cpu_perm0.wf_with(cpu_ptr),
        cpu_perm0.ptr_perm.value().ext_vmpl1 is Some,
{
    let cpu_id = cpu_ptr.borrow(Tracked(&cpu_perm0.ptr_perm)).cpu_id as u32;
    let mut cpu = cpu_ptr.take(Tracked(&mut cpu_perm0.ptr_perm));
    let mut ctx_vmpl1 = cpu.ext_vmpl1.take().unwrap();
    ctx_vmpl1.current_pid = Some(pid);
    ctx_vmpl1.slot_dirty = false;
    ctx_vmpl1.pending_export_pid = None;
    ctx_vmpl1.pending_export_target_cpu = None;
    ctx_vmpl1.pending_export_version = 0;
    cpu.ext_vmpl1 = Some(ctx_vmpl1);
    cpu_ptr.write(Tracked(&mut cpu_perm0.ptr_perm), cpu);

    kdebug!("Bound VMPL1 slot on cpu ", cpu_id, " to pid ", pid);
}

pub(crate) fn stage_fake_vmpl1_handoff_request(
    cpu_ptr: DekoPPtr<DekoCpuCtx>,
    Tracked(cpu_perm0): Tracked<&mut DekoCpuCtxPermission>,
    pid: u32,
    target_cpu: u32,
    version: u64,
)
    requires
        old(cpu_perm0).wf_with(cpu_ptr),
        old(cpu_perm0).ptr_perm.value().ext_vmpl1 is Some,
    ensures
        cpu_perm0.wf_with(cpu_ptr),
        cpu_perm0.ptr_perm.value().ext_vmpl1 is Some,
{
    let cpu_id = cpu_ptr.borrow(Tracked(&cpu_perm0.ptr_perm)).cpu_id as u32;
    let mut cpu = cpu_ptr.take(Tracked(&mut cpu_perm0.ptr_perm));
    let mut ctx_vmpl1 = cpu.ext_vmpl1.take().unwrap();
    ctx_vmpl1.current_pid = Some(pid);
    ctx_vmpl1.slot_dirty = false;
    ctx_vmpl1.pending_export_pid = Some(pid);
    ctx_vmpl1.pending_export_target_cpu = Some(target_cpu);
    ctx_vmpl1.pending_export_version = version;
    cpu.ext_vmpl1 = Some(ctx_vmpl1);
    cpu_ptr.write(Tracked(&mut cpu_perm0.ptr_perm), cpu);

    kdebug!(
        "Staged fake VMPL1 handoff request on cpu ",
        cpu_id,
        " pid=",
        pid,
        " target_cpu=",
        target_cpu,
        " version=",
        version
    );
}

#[verifier::external_body]
pub(crate) fn mark_app_fake_handoff_in_progress(pid: u32, old_cpu: u32) -> DekoGuestServResult<
    u64,
> {
    deko_rwlock_write_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(mut app_list_inner) = app_list {
                if !app_list_inner.contains_key(&pid) {
                    app_list = Some(app_list_inner);
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
                    let mut app = app_list_inner.remove(&pid).unwrap();
                    let version = app.mark_fake_handoff_in_progress(old_cpu);
                    app_list_inner.insert(pid, app);
                    app_list = Some(app_list_inner);
                    Ok(version)
                }
            } else {
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
            }
        }
    }
}

#[verifier::external_body]
pub(crate) fn validate_launch_migration_version(
    pid: u32,
    expected_version: u64,
) -> DekoGuestServResult<()> {
    if expected_version == 0 {
        return Ok(());
    }
    deko_rwlock_read_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(ref app_list_inner) = app_list {
                if let Some(app) = app_list_inner.get(&pid) {
                    if app.ext.state_version == expected_version {
                        Ok(())
                    } else {
                        kwarn!(
                            "Launch app version mismatch: pid=",
                            pid,
                            " expected_version=",
                            expected_version,
                            " actual_version=",
                            app.ext.state_version,
                            " migration_state=",
                            app.ext.migration_state
                        );
                        Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy))
                    }
                } else {
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                }
            } else {
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
            }
        }
    }
}

pub(crate) fn save_app_vmsa_snapshot(pid: u32, vmsa: &VMSA) -> DekoGuestServResult<()> {
    deko_rwlock_write_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(mut app_list_inner) = app_list {
                if !app_list_inner.contains_key(&pid) {
                    app_list = Some(app_list_inner);
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
                    let mut app = app_list_inner.remove(&pid).unwrap();
                    app.save_vmsa_snapshot(vmsa);
                    app_list_inner.insert(pid, app);
                    app_list = Some(app_list_inner);
                    Ok(())
                }
            } else {
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
            }
        }
    }
}

pub(crate) fn get_app_state_version(pid: u32) -> DekoGuestServResult<u64> {
    deko_rwlock_read_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(app_list_inner) = app_list {
                if let Some(app) = app_list_inner.get(&pid) {
                    Ok(app.ext.state_version)
                } else {
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                }
            } else {
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
            }
        }
    }
}

#[verifier::external_body]
pub(crate) fn import_vmpl1_slot_vmsa_from_cpu(pid: u32, source_cpu: u32) -> DekoGuestServResult<
    bool,
> {
    deko_rwlock_read_atomic_data! {
        PERCPU_AREAS,
        percpu_areas,
        percpu_areas_perm,
        {
            let Some(ref percpu_areas) = percpu_areas else {
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
            };
            if source_cpu as usize >= percpu_areas.0.len() {
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
            let shared = &percpu_areas.0[source_cpu as usize];
            if shared.vmpl1_export_pid != Some(pid) {
                Ok(false)
            } else if let Some(vmsa) = shared.vmpl1_export_vmsa.as_ref() {
                save_app_vmsa_snapshot(pid, vmsa)?;
                Ok(true)
            } else {
                Ok(false)
            }
        }
    }
}

#[verifier::external_body]
pub(crate) fn publish_current_cpu_vmpl1_slot_vmsa(
    cpu_index: usize,
    pid: u32,
    version: u64,
    vmsa: &VMSA,
) -> DekoGuestServResult<()> {
    deko_rwlock_write_atomic_data! {
        PERCPU_AREAS,
        percpu_areas,
        percpu_areas_perm,
        {
            let Some(ref mut percpu_areas) = percpu_areas else {
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::Busy));
            };
            if cpu_index >= percpu_areas.0.len() {
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            }
            percpu_areas.0[cpu_index].vmpl1_export_pid = Some(pid);
            percpu_areas.0[cpu_index].vmpl1_export_version = version;
            percpu_areas.0[cpu_index].vmpl1_export_vmsa = Some(*vmsa);
            Ok(())
        }
    }
}

#[verus_spec(r =>
    with
        Tracked(vmsa_page_perm): Tracked<&mut VmsaPagePermission>,
    requires
        old(vmsa).wf(),
        old(vmsa_page_perm).ptr_perm.wf(),
        old(vmsa_page_perm).ptr_perm.is_init(),
        old(vmsa_page_perm).ptr_perm.pptr() == old(vmsa).page@,
    ensures
        vmsa.wf(),
        vmsa_page_perm.ptr_perm.wf(),
        vmsa_page_perm.ptr_perm.is_init(),
        vmsa_page_perm.ptr_perm.pptr() == vmsa.page@,
        r is Ok ==> r.unwrap() ==> vmsa.wf(),
)]
pub(crate) fn restore_app_vmsa_snapshot(pid: u32, vmsa: &mut VmsaPage) -> DekoGuestServResult<
    bool,
> {
    deko_rwlock_read_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(ref app_list_inner) = app_list {
                if let Some(app) = app_list_inner.get(&pid) {
                    if let Some(saved) = app.ext.saved_vmsa.as_ref() {
                        #[verus_spec(with Tracked(vmsa_page_perm))]
                        vmsa.restore_from_snapshot(saved);
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                }
            } else {
                Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
#[verus_spec(
    with
        Tracked(cpu_perm): Tracked<&mut DekoCpuCtxPermission>,
    requires
        old(cpu_perm).wf_with(cpu),
        old(cpu_perm).ptr_perm.value().ext_vmpl1 is Some,
)]
fn run_userapp(
    cpu: DekoPPtr<DekoCpuCtx>,
    ret_params: &mut DekoGuestRequestParams,
) -> DekoGuestServResult<u64> {
    #[verus_spec(
        invariant
            cpu_perm.wf_with(cpu),
            cpu_perm.ptr_perm.value().ext_vmpl1 is Some,
    )]
    loop {
        log_vmpl1_app_binding(cpu);
        // dump_vmpl1_doorbell_snapshot_current_cpu();
        // WARNING: CRITICAL SECTION
        //
        // This requires VMPL switch so we should NEVER enable interrupts here
        // because if there is a #HV doorbell arriving, it will be interrupt
        // right before the VMPL switch and the context gets corrupted.
        //
        // In our current HV handler routine we will actively check if the RFLAGS
        // contains the IF flag; if so, the doorbell will get postponed and the
        // control flow will continue here.
        //
        // Since we do not clear `NoFurtherSignal` here, the KVM will not attempt
        // to inject another interrupt until we re-enable interrupts at the end,
        // which then checks if there is any pending doorbells and processes them.
        // Now copy the information to the VMSA and prepare for the VMPL switch.
        dump_current_cpu_vmpl1_slot_vmsa();
        let switch_ret = no_irq_zone(|| { vmpl_switch(VMPL_GUEST_SECURE_APP) });

        match switch_ret {
            DekoVmplSwitchErr::Ok => {},
            DekoVmplSwitchErr::Cancelled => {
                kinfo!("VMPL switch cancelled; retrying guest entry");
                continue ;
            },
            DekoVmplSwitchErr::Failed => {
                kerror!("VMPL switch failed; retrying guest entry");
                continue ;
            },
        }

        let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
        let cpu_idx = cpu_borrow.cpu_id;
        let vmsa = &cpu_borrow.ext_vmpl1.as_ref().unwrap().vmsa;

        proof_with!(=> Tracked(vmsa_perm));
        let vmsa_ptr = vmsa.ptr();

        proof_with!(Tracked(&vmsa_perm));
        let info = DekoGuestExitInformation::try_parse_vmsa(vmsa_ptr, true);

        let vmsa = vmsa_ptr.borrow(Tracked(&vmsa_perm));
        let snapshot = DekoUserApp::copy_vmsa_snapshot(vmsa);

        kinfo!("Entered guest app in VMPL1, now processing the request: ", info);

        let ret_rax = match get_guest_app_extend_exit_rax(&info) {
            Some(rax) => rax,
            None => {
                kerror!("Unexpected exit from guest app", cpu_idx, info);
                die("");
            },
        };
        *ret_params =
        match get_guest_app_extend_exit_params(&info) {
            Some(params) => params,
            None => {
                kerror!("Missing guest app return params", cpu_idx, info);
                die("");
            },
        };
        if let Some(pid) = cpu_borrow.ext_vmpl1.as_ref().unwrap().current_pid {
            save_app_vmsa_snapshot(pid, &snapshot)?;
        }
        // Attempt to enter the guest only once and if it succeeds, we immediately
        // forward the request to the syscall handler in VMPL2.

        return Ok(ret_rax);
    }
}

#[verifier::external_body]
fn dump_current_cpu_vmpl1_slot_vmsa() {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        kinfo!("VMPL1 slot VMSA dump skipped: no ext_vmpl1");
        return ;
    };

    let vmsa = unsafe { &*(ext_vmpl1.vmsa.vaddr().0 as *const VMSA) };

    kerror!("VMPL1 slot VMSA dump before enter: ", vmsa);
}

fn log_vmpl1_app_binding(_cpu: DekoPPtr<DekoCpuCtx>) {
    let (this_cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = this_cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let cpu_id = cpu_borrow.cpu_id as u32;
    let Some(ext_vmpl1) = cpu_borrow.ext_vmpl1.as_ref() else {
        kinfo!("run_userapp binding: cpu=", cpu_id, " no ext_vmpl1");
        return ;
    };

    let current_pid = ext_vmpl1.current_pid;
    kinfo!(
        "run_userapp slot: cpu=",
        cpu_id,
        " pid=",
        current_pid,
        " slot_dirty=",
        ext_vmpl1.slot_dirty,
        " pending_export_pid=",
        ext_vmpl1.pending_export_pid,
        " pending_export_target_cpu=",
        ext_vmpl1.pending_export_target_cpu,
        " pending_export_version=",
        ext_vmpl1.pending_export_version,
        " last_export_ack_version=",
        ext_vmpl1.last_export_ack_version
    );

    if let Some(pid) = current_pid {
        deko_rwlock_read_atomic_data! {
            DEKO_SHADOW_APP_LIST,
            app_list,
            __,
            {
                if let Some(ref app_list) = app_list {
                    if let Some(app) = app_list.get(&pid) {
                        kinfo!(
                            "run_userapp app: pid=",
                            pid,
                            " owner_cpu=",
                            app.ext.owner_cpu,
                            " loaded_cpu=",
                            app.ext.loaded_cpu,
                            " state_version=",
                            app.ext.state_version,
                            " migration_state=",
                            app.ext.migration_state,
                            " state=",
                            app.ext.state
                        );
                    } else {
                        kinfo!("run_userapp app: pid=", pid, " missing from shadow app list");
                    }
                } else {
                    kinfo!("run_userapp app: shadow app list not initialized");
                }
            }
        }
    }
}

#[verifier::external_body]
#[inline]
fn read_tsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline]
fn get_guest_app_extend_exit_rax(info: &Option<DekoGuestExitInformation>) -> Option<u64> {
    match info {
        Some(DekoGuestExitInformation::ServiceRequest { protocol, req, params }) if *protocol
            == DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE => {
            if *req == DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER
                && params.additional_data.is_some() {
                Some(0)
            } else if *req == DEKO_SERVICE_EXTEND_TIMER_EVENT {
                Some(DEKO_SERVICE_TIMER)
            } else {
                None
            }
        },
        _ => None,
    }
}

#[inline]
fn get_guest_app_extend_exit_params(info: &Option<DekoGuestExitInformation>) -> Option<
    DekoGuestRequestParams,
> {
    match info {
        Some(DekoGuestExitInformation::ServiceRequest { protocol, req, params }) if *protocol
            == DEKO_GUEST_EXIT_PROTOCOL_EXTEND_SERVICE => {
            if *req == DEKO_SERVICE_EXTEND_INVOKE_UNTRUSTED_SYSCALL_HANDLER
                && params.additional_data.is_some() {
                Some(*params)
            } else if *req == DEKO_SERVICE_EXTEND_TIMER_EVENT {
                Some(*params)
            } else {
                None
            }
        },
        _ => None,
    }
}

/// Called at VMPL1. This sets up some necessary state for the user application
/// before jumping to the original entry point.
#[verus_spec(
    requires

)]
#[verifier::exec_allows_no_decreases_clause]
pub fn setup_vmpl1() {
    let (cpu, Tracked(mut cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    if cpu_borrow.ext_vmpl1.is_none() {
        return ;
    }
    let private_bit = cpu_borrow.private_bit;
    let shared_bit = cpu_borrow.shared_bit;
    let ext = cpu_borrow.ext_vmpl1.as_ref().unwrap();
    let ghcb_gpa = match virt_to_phys_checked(
        private_bit,
        shared_bit,
        ext.ghcb.into_vaddr(),
        Tracked(&cpu_perm.pgtable_perm),
    ) {
        Some(gpa) => gpa,
        None => return ,
    };
    msr_register_ghcb_gpa(ghcb_gpa);
    init_ghcb_logging(0x3f8);

    kinfo!("setup_vmpl1: GHCB registered @", ghcb_gpa=>hex);

    // Register the doorbell.
    let (ghcb, Tracked(ghcb_perm), pa) = current_ghcb();
    GuestHostCommunicationBlock::register_hv_doorbell(
        ghcb,
        Tracked(ghcb_perm),
        ext.doorbell_pa,
        pa,
    );

    kinfo!("setup_vmpl1: #HV doorbell registered @", ext.doorbell_pa=>hex);

    let db_ptr = ext.doorbell.acquire_read();
    init_hv_doorbell_vmpl1();

    db_ptr.release_read();

    wait_ipi_blocking();  // ensure all cores are synchronized.

    loop {
        // As this function never returns we place the loop here.
        no_irq_zone(
            ||
                {
                    // We have finished the VMPL1 setup. Now we switch context to the target payload
                    // (e.g., the actual Guest OS or the Monitor loop).
                    //
                    // This is typically a one-way transition.
                    vmpl_switch(VMPL_GUEST_DEKO_MONITOR)
                },
        );
    }

    die("setup_vmpl1: this should never return");
}

func_ptr!(setup_vmpl1);

} // verus!
