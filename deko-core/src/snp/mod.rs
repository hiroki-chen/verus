use core::ops::Range;
use core::sync::atomic::AtomicU32;

use deko_macros::{deko_const_decl, with_atomic_pred, DekoDebug};
use deko_std::prelude::*;
use deko_std::wf::WellFormed;
use vstd::cell::PCell;
use vstd::invariant;
use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

use crate::collections::{get_unchecked, Vec};
use crate::cpu::apic::Apic;
use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::irq::{raw_irq_enable, DekoUnsafeRwLock, IrqState, IrqUnSafeLockGuard};
use crate::cpu::{
    CpuidTable, DekoCpuCtx, DekoCpuCtxPermission, PerCpuAreas, PerCpuShared, CPUID_MAX_COUNT,
    CPU_AREA_MAGIC, PERCPU_AREAS,
};
use crate::fw::get_fw_regions_from_igvm;
use crate::mm::paging::{PageTablePermission, PteFlags};
use crate::mm::vm::TempMapping;
use crate::mm::{
    init_guest_mmap, phys_to_virt, virt_to_phys, zero_page, PageEncryptionMasks,
    DEKO_FRAME_ALLOCATOR, FEATURE_MASK, MAX_PHYS_ADDR, PHYS_ADDR_SIZE, PTE_MASK_PRIVATE,
    PTE_MASK_SHARED,
};
use crate::snp::doorbell::init_hv_doorbell;
use crate::snp::ghcb::{current_ghcb, msr_register_ghcb_gpa, GuestHostCommunicationBlock};
use crate::snp::vmsa::VMSA;
use crate::{
    die, kdebug, kerror, kinfo, kpanic_if, ktrace, kwarn, vec, DekoKernelLaunchInfo,
    Stage2LaunchInfo,
};

pub mod doorbell;
pub mod ghcb;
pub mod logging;
pub mod req;
pub mod rmp;
pub mod vmsa;

extern "C" {
    /// A global flag to indicate whether the AP has been started.
    static mut ap_flag: AtomicU32;
    #[link_name = "snp_idle_halt"]
    fn __snp_idle_halt(doorbell: *const doorbell::HVDoorbell);
}

verus! {

#[derive(DekoDebug, Clone, Copy)]
pub enum PageStateChangeOp {
    Private,
    Shared,
    Psmash,
    Unsmash,
}

/// Illegal input parameters
pub(crate) const PVALIDATE_FAIL_INPUT: u64 = 0x1;

/// Page size mismatch between guest (2M) and RMP entry (4K)
pub(crate) const PVALIDATE_SIZEMISMATCH: u64 = 0x6;

pub(crate) const PSC_OP_SHIFT: u8 = 52;

pub(crate) const PSC_OP_PRIVATE: u64 = 1 << PSC_OP_SHIFT;

pub(crate) const PSC_OP_SHARED: u64 = 2 << PSC_OP_SHIFT;

pub(crate) const PSC_OP_PSMASH: u64 = 3 << PSC_OP_SHIFT;

pub(crate) const PSC_OP_UNSMASH: u64 = 4 << PSC_OP_SHIFT;

pub(crate) const PSC_FLAG_HUGE_SHIFT: u8 = 56;

pub(crate) const PSC_FLAG_HUGE: u64 = 1 << PSC_FLAG_HUGE_SHIFT;

pub(crate) const GHCB_BUFFER_SIZE: usize = 0x7f0;

pub(crate) spec const PSC_GFN_MASK_SPEC: u64 = (((1u64 << 52) - 1) as u64) & !0xfffu64;

#[verifier::when_used_as_spec(PSC_GFN_MASK_SPEC)]
pub(crate) exec const PSC_GFN_MASK: u64
    ensures
        PSC_GFN_MASK == PSC_GFN_MASK_SPEC,
{
    proof {
        assert((1u64 << 52) - 1 >= 0) by (bit_vector);
    }

    ((1u64 << 52) - 1) & !0xfffu64
}

deko_bitflags! {
    /// RMP (Reverse Map Table) entry flags.
    pub struct Rmp: u32 {
        const VMPL_LOW = 0;
        const VMPL_HIGH = 1;
        const READ = 8;
        const WRITE = 9;
        const X_USER = 10;
        const X_SUPER = 11;
        const BIT_VMSA = 16;
    }
}

deko_bitflags_quick! {
    Rmp,
    vmpl0: { 0 },
    vmpl1: { VMPL_LOW },
    vmpl2: { VMPL_HIGH },
    vmpl3: { VMPL_LOW, VMPL_HIGH },
    vmsa: { BIT_VMSA, READ },
    rwx: { READ, WRITE, X_USER, X_SUPER },
    rwx_guest_vmpl2: { VMPL_HIGH, READ, WRITE, X_USER, X_SUPER },
}

pub const VMPCK_SIZE: usize = 32;

pub const VMPL_MAX: usize = 4;

/// Initialize the secrets page at the given virtual address.
#[verifier::external_body]
#[verus_spec(
    with
        Tracked(cpu_ctx): Tracked<&DekoCpuCtxPermission>,
    requires
        addr.wf(),
        cpu_ctx.pgtable_perm.mapped(addr),
)]
pub fn init_secrets_page(addr: VirtAddr) {
    let mut write_handle = SECRETS_PAGE.acquire_write();
    SecretsPage::copy_from_rwlock(&mut write_handle, addr);
    write_handle.release_write_no_val();

    unsafe {
        // Zero out the source secrets page to avoid leakage.
        core::ptr::write_bytes(addr.0 as *mut u8, 0, core::mem::size_of::<SecretsPage>());
    }
}

pub exec static SECRETS_PAGE: DekoUnsafeRwLock<SecretsPage, SecretsPagePermission, SecretsPagePred>
    ensures
        SECRETS_PAGE.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new_with(SecretsPage::new(), Tracked(SecretsPagePermission {  })),
        IrqUnSafeLockGuard {  },
        Ghost(SecretsPagePred {  }),
    );

    proof {
        use_type_invariant(&r);
    }

    r
}

#[derive(Copy, Clone, DekoDebug)]
#[repr(C, packed)]
pub struct SecretsPage {
    version: u32,
    gctxt: u32,
    fms: u32,
    reserved_00c: u32,
    gosvw: [u8; 16],
    vmpck: [[u8; VMPCK_SIZE]; VMPL_MAX],
    reserved_0a0: [u8; 96],
    vmsa_tweak_bmp: [u64; 8],
    svsm_base: u64,
    svsm_size: u64,
    svsm_caa: u64,
    svsm_max_version: u32,
    svsm_guest_vmpl: u8,
    reserved_15d: [u8; 3],
    tsc_factor: u32,
    reserved_164: [u8; 3740],
}

with_permission! {
    SecretsPage,
}

with_atomic_pred! {
    SecretsPage,
    SecretsPagePermission,
}

impl SecretsPage {
    pub const fn new() -> (r: Self)
        ensures
            r.wf(),
    {
        SecretsPage {
            version: 0,
            gctxt: 0,
            fms: 0,
            reserved_00c: 0,
            gosvw: [0;16],
            vmpck: [[0;VMPCK_SIZE];VMPL_MAX],
            reserved_0a0: [0;96],
            vmsa_tweak_bmp: [0;8],
            svsm_base: 0,
            svsm_size: 0,
            svsm_caa: 0,
            svsm_max_version: 0,
            svsm_guest_vmpl: 0,
            reserved_15d: [0;3],
            tsc_factor: 0,
            reserved_164: [0;3740],
        }
    }
}

#[verus_verify]
impl SecretsPage {
    /// Copy the secrets page from the given virtual address.
    #[verifier::external_body]
    #[inline(always)]
    #[verus_spec(
        with
            Tracked(pgtable_perm): Tracked<&PageTablePermission>
        requires
            pgtable_perm.mapped(from),
            from.wf(),
            old(this).is_init(),
        ensures
            this.is_init(),
    )]
    pub fn copy_from_rwlock(
        this: &mut WriteHandle<
            '_,
            DekoAtomicData<Self, SecretsPagePermission>,
            IrqUnSafeLockGuard,
            SecretsPagePred,
        >,
        from: VirtAddr,
    ) {
        proof_with!(Tracked(pgtable_perm));
        Self::copy_from_ptr(this.as_ptr(), from);
    }

    /// Copy the secrets page from the given virtual address.
    ///
    /// This function expects a [`PPtr`] to the atomic data so
    /// we do not need to acquire [`vstd::simple_pptr::PointsTo<V>`]
    /// permission again since the safety is already guaranteed by
    /// the sync primitives (we do not have other ways to obtain the
    /// raw pointer unless a lock is acquired).
    #[inline(always)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(pgtable_perm): Tracked<&PageTablePermission>
        requires
            pgtable_perm.mapped(from),
            from.wf(),
    )]
    fn copy_from_ptr(
        this: PPtr<DekoAtomicData<SecretsPage, SecretsPagePermission>>,
        from: VirtAddr,
    ) {
        unsafe {
            core::ptr::copy_nonoverlapping(
                from.0 as *const SecretsPage,
                this.addr() as *mut SecretsPage,
                1,
            );
        }
    }
}

impl WellFormed for SecretsPage {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

#[inline(always)]
#[verifier::external_body]
#[verus_spec(r =>
    requires
        header.wf(),
    ensures
        r.wf(),
        r == header.get_igvm_param_block_spec(),
)]
pub fn get_igvm_params_block<'a>(header: &'a Stage2LaunchInfo) -> &'a IgvmParamBlock {
    // Note that this case does NOT include all the fields contained in the
    // `header.igvm_params` structure; we just extract the leading `IgvmParamBlock`
    // here since it is the first part of the structure; this should be safe as long
    // as we do not access any fields beyond the `IgvmParamBlock` fields.
    unsafe { &*(header.igvm_params as *const IgvmParamBlock) }
}

fn has_vtom() -> bool {
    let snp_status = SnpStatusFlags::get_status();
    proof {
        lemma_SnpStatus_bit_valid(VTOM as _);
    }

    snp_status.contains(VTOM)
}

pub exec static SNP_VTOM: DekoSimpleOnceCell<usize>
    ensures
        SNP_VTOM.wf(),
{
    DekoSimpleOnceCell::new(Ghost(()))
}

pub const MSR_SEV_STATUS: u32 = 0xC001_0131;

/// The MSR used to support the GHCB MSR Protocol. For more
/// details, please refer to SEV-ES GHCB standardization doc
/// published by AMD.
pub const MSR_AMD64_SEV_ES_GHCB: u32 = 0xC001_0130;

#[inline(always)]
fn get_page_encryption_masks() -> PageEncryptionMasks {
    if has_vtom() {
        crate::die("We do not support VTOM yet");
    } else {
        PageEncryptionMasks {
            private_pte_mask: 1 << 51,  // <- perhaps we can get it from assembly.
            shared_pte_mask: 0,
            addr_mask_width: 51,
            phys_addr_sizes: 48,  // todo: do not hardcode this.
        }
    }
}

pub fn init_platform(header: Stage2LaunchInfo)
    requires
        header.wf(),
{
    // Set the top of the virtual memory.
    let vtom = header.vtom as usize;
    SNP_VTOM.init(vtom);

    // Set the encryption bit.
    let masks = get_page_encryption_masks();
    PTE_MASK_PRIVATE.init(masks.private_pte_mask);
    PTE_MASK_SHARED.init(masks.shared_pte_mask);

    let guest_phys_addr_size = (masks.phys_addr_sizes >> 16) & 0xff;
    let host_phys_addr_size = masks.phys_addr_sizes & 0xff;
    let phys_addr_size = if guest_phys_addr_size == 0 {
        // When [GuestPhysAddrSize] is zero, refer to the PhysAddrSize field
        // for the maximum guest physical address size.
        // - APM3, E.4.7 Function 8000_0008h - Processor Capacity Parameters and Extended Feature Identification
        host_phys_addr_size
    } else {
        guest_phys_addr_size
    };

    PHYS_ADDR_SIZE.init(phys_addr_size);

    // If the C-bit is a physical address bit however, the guest physical
    // address space is effectively reduced by 1 bit.
    // - APM2, 15.34.6 Page Table Support
    let effective_phys_addr_size = if masks.addr_mask_width <= phys_addr_size {
        masks.addr_mask_width
    } else {
        phys_addr_size
    };

    assume(effective_phys_addr_size < u32::BITS);  // ugly workaround.

    let max_addr = 1 << effective_phys_addr_size;
    MAX_PHYS_ADDR.init(max_addr);

    // Initialize feature masks.
    let mut feature_mask = PteFlags::all_bits();
    // feature_mask.remove(PteFlags::GLOBAL);

    FEATURE_MASK.init(feature_mask);
}

#[verifier::spinoff_prover]
pub fn validate_memory(
    Tracked(ctx_perm): Tracked<&mut DekoCtxPermission>,
    heap_start: u64,
    heap_end: u64,
) -> (r: bool)
    requires
        old(ctx_perm).wf(),
        old(ctx_perm).pgtable_perm.mapped_region(VirtAddr(heap_start)..VirtAddr(heap_end)),
        heap_end > heap_start,
        heap_start % PAGE_SIZE == 0,
        heap_end % PAGE_SIZE == 0,
        heap_end <= LOWMEM_END as u64,
    ensures
        ctx_perm.wf(),
        old(ctx_perm).deko_ctx_ptr_perm.pptr() === ctx_perm.deko_ctx_ptr_perm.pptr(),
        old(ctx_perm).private_bit() == ctx_perm.private_bit(),
        old(ctx_perm).shared_bit() == ctx_perm.shared_bit(),
{
    let mut cur = heap_start;

    while cur < heap_end
        invariant
            heap_start <= cur <= heap_end,
            ctx_perm.wf(),
            cur % PAGE_SIZE == 0,
            heap_start % PAGE_SIZE == 0,
            heap_end % PAGE_SIZE == 0,
            PAGE_SIZE == 0x1000,
            heap_end <= LOWMEM_END as u64,
            old(ctx_perm).deko_ctx_ptr_perm.pptr() === ctx_perm.deko_ctx_ptr_perm.pptr(),
            old(ctx_perm).private_bit() == ctx_perm.private_bit(),
            old(ctx_perm).shared_bit() == ctx_perm.shared_bit(),
            old(ctx_perm).pgtable_perm == ctx_perm.pgtable_perm,
            old(ctx_perm).pgtable_perm.mapped_region(VirtAddr(heap_start)..VirtAddr(heap_end)),
        decreases heap_end - cur,
    {
        // check if this address is aligned with 2MB page?
        let addr = VirtAddr::new(cur);

        proof {
            // Prove that the canonicalized address is also aligned to 4K.
            VirtAddr::lemma_make_canonical_preserves_alignment_4k(cur, addr@);
        }

        let (ret, cf) = pvalidate(addr.0, PAGE_SIZE, true, Tracked(&mut ctx_perm.pgtable_perm));

        if ret != 0 || !cf {
            return false;
        }
        cur += PAGE_SIZE;
    }

    true
}

// Constants from snpcall.rs
pub const RMP_4K: u64 = 0;

pub const RMP_2M: u64 = 1;

pub const RMP_READ: u8 = 1;

pub const RMP_WRITE: u8 = 2;

pub const RMP_USER_EXE: u8 = 4;

pub const RMP_KERN_EXE: u8 = 8;

pub const RMP_NO_WRITE: u8 = RMP_READ | RMP_USER_EXE | RMP_KERN_EXE;

pub const RMP_RWX: u8 = RMP_NO_WRITE | RMP_WRITE;

/// Set up the GHCB pages and other necessary state for SNP operation.
pub fn init_guest_host(
    ctx: DekoPPtr<DekoCpuCtx>,
    Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
)
    requires
        old(ctx_perm).wf_with(ctx),
    ensures
        ctx_perm.wf_with(ctx),
{
    crate::snp::ghcb::validate_ghcb(ctx, Tracked(ctx_perm));
}

pub fn init_platform_end(
    igvm_params: &IgvmParamBlock,
    Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
)
    requires
        igvm_params.wf(),
        old(ctx_perm).ghcb_perm.wf(),
        old(ctx_perm).pgtable_perm.wf(),
        old(ctx_perm).ptr_perm.wf(),
    ensures
        ctx_perm == old(ctx_perm),  /* fix later. */
{
    let debug_console_port = igvm_params.debug_serial_port as u16;
    crate::snp::logging::init_ghcb_logging(debug_console_port);

    // Print IGVM parameter information for debugging
    kdebug!("IGVM Parameters\n\t", igvm_params);

    kinfo!("enabled interrupt?", crate::cpu::irq::rflags() => hex);
}

pub fn init_each_cpu(ctx: DekoPPtr<DekoCtx>, Tracked(ctx_perm): Tracked<DekoCtxPermission>) -> (r: (
    DekoPPtr<DekoCpuCtx>,
    Tracked<DekoCpuCtxPermission>,
))
    requires
        ctx_perm.wf_with(ctx),
    ensures
        r.1@.wf_with(r.0),
        r.1@.pgtable_perm.private_bit == ctx_perm.private_bit(),
        r.1@.pgtable_perm.shared_bit == ctx_perm.shared_bit(),
        r.1@.pgtable_perm.mapping_space == ctx_perm.mapping_space,
{
    // 1. First we set up the GHCB page for this CPU.
    // Get the page table from the context that was passed in
    let bsp_pgtable = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).pgtable;
    let tracked bsp_pgtable_perm = &ctx_perm.pgtable_perm;
    let (ghcb, Tracked(ghcb_perm)) = Box::<GuestHostCommunicationBlock>::new_zeroed(
        &DEKO_FRAME_ALLOCATOR,
    );
    let (ghcb, Tracked(ghcb_perm)) = ghcb.into_ptr(Tracked(ghcb_perm));

    // 2. We now set up the percpu area for this CPU.
    // Note that we do not need to initialize the percpu area since it is
    // zeroed out by Box::new_zeroed.
    // We just need to set up the page table entry and the CpuData struct.
    let (bsp_percpu, Tracked(bsp_percpu_perm)) = Box::new_zeroed(&DEKO_FRAME_ALLOCATOR);
    let bsp_percpu_paddr = PhysAddr(bsp_percpu.addr() as u64);
    let (bsp_percpu_ptr, Tracked(mut bsp_percpu_perm)) = bsp_percpu.into_ptr(
        Tracked(bsp_percpu_perm),
    );

    // 3. Initialize the percpu area.
    // Get the platform-specific PTE mask values for this CPU
    let masks = get_page_encryption_masks();

    let (irq_state, Tracked(irq_state_perm)) = IrqState::new();
    // Use the existing context that was passed in from setup_env
    // This context already has the proper stage2_launch_info and other components
    let bsp_percpu = DekoCpuCtx::new(
        bsp_pgtable,
        ghcb,
        0,  // cpu_id
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).shared_bit,
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).private_bit,
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).mapping_space,
        None,  // vm_region
        None,  // ctx_switch_stack
        None,  // ist_stack
        None,
        None,
        irq_state,
    );
    bsp_percpu_ptr.write(Tracked(&mut bsp_percpu_perm), bsp_percpu);

    let tracked mut cpu_ctx_perm = DekoCpuCtxPermission {
        ptr_perm: bsp_percpu_perm,
        pgtable_perm: ctx_perm.pgtable_perm,
        ghcb_perm,
        vm_region_perm: None,
        irq_state_perm,
    };

    assume(cpu_ctx_perm.wf_with(bsp_percpu_ptr));

    // 4. This maps the PERCPU_BASE addr to the percpu area so `this_cpu` workds.
    DekoCpuCtx::map_page_4k(
        bsp_percpu_ptr,
        Tracked(&mut cpu_ctx_perm),
        PERCPU_BASE,
        bsp_percpu_paddr,
        PteFlags::data(),
    );

    init_guest_host(bsp_percpu_ptr, Tracked(&mut cpu_ctx_perm));

    (bsp_percpu_ptr, Tracked(cpu_ctx_perm))
}

/// Marks all pages within `vrange` as valid/invalid in the RMP table.
///
/// The operation is not `unsafe` as in the precondition we ensure that
/// the caller has the necessary permissions to perform this operation
/// and that the addresses within `vrange` are mapped in the page table
/// so that `rmpadjust` will not page fault.
#[verus_spec(r =>
    with
        Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>
    requires
        old(ctx_perm).wf(),
        old(ctx_perm).pgtable_perm.mapped_region(vrange),
        vrange.wf(),
        vrange.start@ % PAGE_SIZE == 0,
        vrange.end@ % PAGE_SIZE == 0,
    ensures
        if validate { true } else { true },  // TODO: fill in later.
        ctx_perm.wf(),
        ctx_perm.pgtable_perm.mapped_region(vrange),
        ctx_perm.pgtable_perm.mapping_space == old(ctx_perm).pgtable_perm.mapping_space,
)]
pub fn validate_vaddr_region(vrange: VaddrRange, validate: bool) {
    broadcast use vstd::arithmetic::div_mod::lemma_mod_equivalence;

    let mut cur = vrange.start.0;
    let end = vrange.end.0;

    proof {
        assert(end % PAGE_SIZE == 0);
        assert(cur % PAGE_SIZE == 0);
        assert(((end - cur)) % PAGE_SIZE as int == 0);
    }

    while cur < end
        invariant
            vrange.start@ <= cur <= end,
            end == vrange.end@,
            ctx_perm.wf(),
            ctx_perm.pgtable_perm.mapped_region(vrange),
            ctx_perm.pgtable_perm.mapping_space == old(ctx_perm).pgtable_perm.mapping_space,
            vrange.wf(),
            vrange.start@ % PAGE_SIZE == 0,
            vrange.end@ % PAGE_SIZE == 0,
            cur % PAGE_SIZE == 0,
            ((end - cur) as u64) % PAGE_SIZE == 0,
            PAGE_SIZE == PAGE_SIZE,  // <- important: must inline it.

        decreases end - cur,
    {
        let tracked prev_ctx_perm = &*ctx_perm;
        proof {
            ctx_perm.pgtable_perm.lemma_mapped_region_implies_mapped(vrange, VirtAddr(cur));
        }
        let (ret, changed) = pvalidate(
            cur,
            PAGE_SIZE,
            validate,
            Tracked(&mut ctx_perm.pgtable_perm),
        );
        if ret != 0 || !changed {
            kerror!("RMPVALIDATE failed for vaddr regions");
            die("RMPVALIDATE failed");
        }
        proof {
            assert(forall|v: VirtAddr|
                vrange.start@ <= v@ < vrange.end@ && v@ % PAGE_SIZE == 0
                    ==> prev_ctx_perm.pgtable_perm.mapped(v)
                    ==> #[trigger] ctx_perm.pgtable_perm.mapped(v));
            ctx_perm.pgtable_perm.lemma_mapped_region_implies_mapped(vrange, VirtAddr(cur));
        }
        cur += PAGE_SIZE;
    }
}

/// PVALIDATE takes a page size as an input parameter indicating that either a
/// 4KB or 2MB page should be validated.
///
/// If the guest attempts to validate a page that is not mapped to the specified size,
/// e.g., a 4KB page is specified but the address is mapped to a 2MB page, a `VMEXIT`
/// will occur to indicate an NPF. The reverse will generate a `FAIL_SIZE_MISMATCH`.
///
/// Returns the return value and the changed bit of CF.
#[verifier::external_body]
pub fn pvalidate(
    vaddr: u64,
    psize: u64,
    validate: bool,
    Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
) -> (r: (u64, bool))
    requires
        psize == PAGE_SIZE || psize == PAGE_SIZE_2M,  // Either 4K or 2M page.
        vaddr % PAGE_SIZE == 0,
        old(pgtable_perm).wf(),
        old(pgtable_perm).mapped(VirtAddr(vaddr)),
    ensures
        old(pgtable_perm) == pgtable_perm,
{
    let ret: u64;
    let rcx = if psize == PAGE_SIZE {
        RMP_4K
    } else {
        RMP_2M
    };
    let changed: u8;
    let rdx = if validate {
        1
    } else {
        0
    };

    unsafe {
        core::arch::asm!(
            "pvalidate",
            "setc {cf}",
            inlateout("rax") vaddr => ret,
            in("rcx")  rcx,
            in("rdx")  rdx,
            cf = out(reg_byte) changed,
            options(att_syntax, nostack));
    }

    (ret, changed == 0)  // if cf == 0 then we are ok.

}

/// Adjusts the RMP entry for the given virtual address range => RMP can be used to
/// change the permissions of a page (e.g., from private to shared).
#[verifier::external_body]
pub fn rmpadjust(
    vaddr: VirtAddr,
    psize: u64,
    flags: RmpFlags,
    Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
) -> (r: u64)
    requires
        vaddr.wf(),
        vaddr@ % PAGE_SIZE == 0,
        old(pgtable_perm).wf(),
        old(pgtable_perm).mapped(vaddr),
        flags.wf(),
        flags.bits() & Rmp_ALL_BITS == flags.bits(),
        psize == PAGE_SIZE || psize == PAGE_SIZE_2M,
    ensures
        old(pgtable_perm) == pgtable_perm,
{
    let ret: u64;

    unsafe {
        core::arch::asm!(
            "rmpadjust",
            inout("rax") vaddr.0 => ret,
            inout("rcx") psize => _,
            in("rdx") flags.bits(),
            options(nostack, att_syntax)
        );
    }

    ret
}

pub fn rdmsr(msr: u32) -> u64 {
    let (ghcb, Tracked(perm)) = current_ghcb();

    let (low, high, _) = GuestHostCommunicationBlock::rdmsr(ghcb, Tracked(perm), msr);

    ((high as u64) << 32) | (low as u64)
}

pub fn wrmsr(msr: u32, value: u64) {
    let (ghcb, Tracked(perm)) = current_ghcb();

    let low = value as u32;
    let high = (value >> 32) as u32;

    GuestHostCommunicationBlock::wrmsr(ghcb, Tracked(perm), msr, high, low);
}

/// Sets up the local APIC for the current CPU.
pub fn setup_apic(ctx: DekoPPtr<DekoCpuCtx>, Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>)
    requires
        old(ctx_perm).wf_with(ctx),
    ensures
        ctx_perm.wf_with(ctx),
        ctx_perm.ptr_perm == old(ctx_perm).ptr_perm,
{
    broadcast use SnpStatusFlags::lemma_each_bit_is_valid;
    // Use the restricted interrupt mode.

    if SnpStatusFlags::get_status().contains(REST_INJ) {
        kinfo!("SNP: Using restricted interrupt mode");
        doorbell::HVDoorbell::allocate();
    }
    let apic = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).apic();

    // Enable x2APIC mode
    apic.enable();
    // Enable the Spurious Interrupt Vector
    apic.sw_enable();
}

// verus!
// FIXME: This macro generated lemmas that might take too long to verify.
// We temporarily add rlimit(infinity) but need to optimize it later.
deko_bitflags! {
    pub struct SnpStatus: u64 {
        const SEV = 0;
        const SEV_ES = 1;
        const SEV_SNP = 2;
        const VTOM = 3;
        const REFLECT_VS = 4;
        const REST_INJ = 5;
        const ALT_INJ = 6;
        const DBG_SWP = 7;
        const PREV_HOST_IBS = 8;
        const BTB_ISOLATION = 9;
        const VMPL_SSS = 10;
        const SECURE_TSC = 11;
        const VMGEXIT_PARAM = 12;
        const PMC_VIRT = 13;
        const IBS_VIRT = 14;
        const GUEST_MSR_INTERCEPT = 15;
        const VMSA_REG_PROT = 16;
    }
}

verus! {

impl SnpStatusFlags {
    /// Read the SNP status from the MSR; as this is MSR read, we mark this
    /// as `external_body`.
    #[verifier::external_body]
    #[inline(always)]
    pub fn get_status() -> (r: Self)
        ensures
            r.wf(),
            r.bits() & SnpStatus_ALL_BITS == r.bits(),
    {
        let bits = read_msr(MSR_SEV_STATUS);

        Self::from_bits_truncate(bits)
    }
}

#[inline]
pub fn outw(port: u16, val: u16) {
    let (ghcb, Tracked(perm)) = current_ghcb();
    GuestHostCommunicationBlock::ioout(ghcb, Tracked(perm), port, val as _, 2);
}

#[inline]
pub fn inb(port: u16) -> u8 {
    let (ghcb, Tracked(perm)) = current_ghcb();
    GuestHostCommunicationBlock::ioin(ghcb, Tracked(perm), port, 1) as u8
}

#[inline]
pub fn inw(port: u16) -> u16 {
    let (ghcb, Tracked(perm)) = current_ghcb();
    GuestHostCommunicationBlock::ioin(ghcb, Tracked(perm), port, 2) as u16
}

#[inline]
pub fn inl(port: u16) -> u32 {
    let (ghcb, Tracked(perm)) = current_ghcb();
    GuestHostCommunicationBlock::ioin(ghcb, Tracked(perm), port, 3) as u32
}

#[derive(DekoDebug)]
pub struct SevFWMetaData {
    pub cpuid_page: Option<PhysAddr>,
    pub secrets_page: Option<PhysAddr>,
    pub caa_page: Option<PhysAddr>,
    pub valid_mem: Vec<PaddrRange>,
}

impl WellFormed for SevFWMetaData {
    /// Please note that we do not requires that
    /// all valid memories in the `valid_mem` are properly sorted.
    open spec fn wf(&self) -> bool {
        &&& self.secrets_page.wf()
        &&& self.secrets_page matches Some(p) ==> p@ % PAGE_SIZE == 0 && p@ <= 0x8000_0000
        &&& self.cpuid_page.wf()
        &&& self.cpuid_page matches Some(p) ==> p@ % PAGE_SIZE == 0 && p@ <= 0x8000_0000
        &&& self.caa_page.wf()
        &&& self.caa_page matches Some(p) ==> p@ % PAGE_SIZE == 0 && p@ <= 0x8000_0000
        &&& forall|i: int|
        // 1. Each should be well-formed.

            #![trigger self.valid_mem[i]]
            0 <= i < self.valid_mem@.len() as int ==> {
                &&& self.valid_mem@[i].wf()
                &&& self.valid_mem@[i].start@ % PAGE_SIZE == 0
                &&& self.valid_mem@[i].end@ % PAGE_SIZE == 0
                &&& self.cpuid_page matches Some(cpuid_p) ==> !(self.valid_mem@[i].start@
                    <= cpuid_p@ && cpuid_p@ < self.valid_mem@[i].end@)
                &&& self.secrets_page matches Some(secrets_p) ==> !(self.valid_mem@[i].start@
                    <= secrets_p@ && secrets_p@ < self.valid_mem@[i].end@)
                &&& self.caa_page matches Some(caa_p) ==> !(self.valid_mem@[i].start@ <= caa_p@
                    && caa_p@ < self.valid_mem@[i].end@)
            }
            // 2. these cpuid_page should never overlap.
        &&& forall|i: int, j: int|
            #![trigger self.valid_mem@[i], self.valid_mem@[j]]
            0 <= i < self.valid_mem@.len() as int && 0 <= j < self.valid_mem@.len() as int && i != j
                ==> self.valid_mem@[i].start@ >= self.valid_mem@[j].end@
                || self.valid_mem@[j].start@ >= self.valid_mem@[i].end@
    }
}

/// Fetches the SEV firmware metadata from the IGVM parameter block.
#[verus_spec(r =>
    requires
        igvm_params.wf(),
    ensures
        r.wf(),
)]
pub fn get_sev_fw_metadata(igvm_params: &IgvmParamBlock) -> Option<SevFWMetaData> {
    if igvm_params.firmware.size != 0 {
        if igvm_params.firmware.prevalidated_count > 8 {
            return None;
        }
        let mut cpuid_page = None;
        let mut secrets_page = None;
        let mut caa_page = None;
        let mut valid_mem: alloc::vec::Vec<
            Range<PhysAddr>,
            crate::mm::frame_allocator::DekoAllocatorApi,
        > = vec![];

        if igvm_params.firmware.caa_page != 0 {
            if igvm_params.firmware.caa_page as u64 % PAGE_SIZE != 0 {
                kwarn!("SEV FW Metadata: CAA page is not aligned to PAGE_SIZE");
                return None;
            }
            caa_page = Some(PhysAddr(igvm_params.firmware.caa_page as u64));
        }
        if igvm_params.firmware.cpuid_page != 0 {
            if igvm_params.firmware.cpuid_page as u64 % PAGE_SIZE != 0 {
                kwarn!("SEV FW Metadata: CPUID page is not aligned to PAGE_SIZE");
                return None;
            }
            cpuid_page = Some(PhysAddr(igvm_params.firmware.cpuid_page as u64));
        }
        if igvm_params.firmware.secrets_page != 0 {
            if igvm_params.firmware.secrets_page as u64 % PAGE_SIZE != 0 {
                kwarn!("SEV FW Metadata: Secrets page is not aligned to PAGE_SIZE");
                return None;
            }
            secrets_page = Some(PhysAddr(igvm_params.firmware.secrets_page as u64));
        }
        for i in 0..igvm_params.firmware.prevalidated_count as usize
            invariant
                i <= igvm_params.firmware.prevalidated_count as usize,
                igvm_params.wf(),
                valid_mem@.len() == i as int,
                // This is sufficient for deriving that the final result is well-formed.
                forall|j: int|
                    #![trigger valid_mem@[j]]
                    0 <= j < valid_mem@.len() ==> {
                        &&& valid_mem@[j].start@
                            == igvm_params.firmware.prevalidated@[j].base as u64
                        &&& valid_mem@[j].end@ == (igvm_params.firmware.prevalidated@[j].base as u64
                            + igvm_params.firmware.prevalidated@[j].size as u64)
                    },
        {
            let this = igvm_params.firmware.prevalidated.index(i);

            // This is by guarantee of the igvmbuilder and also stated in the
            // verification precondition and this can be very rare; for safety
            // we just skip this entry and make this path cold.
            if core::hint::unlikely(this.size == 0) {
                kwarn!("SEV FW Metadata: Prevalidated memory region has size 0");
                return None;
            }
            if core::hint::unlikely(
                this.base as u64 % PAGE_SIZE != 0 || this.size as u64 % PAGE_SIZE != 0,
            ) {
                kwarn!("SEV FW Metadata: Prevalidated memory region is not aligned to `PAGE_SIZE`");
                return None;
            }
            let prange = PaddrRange {
                start: PhysAddr(this.base as u64),
                end: PhysAddr(this.base as u64 + this.size as u64),
            };
            proof {
                assert(prange.wf()) by {
                    assert(this.base + this.base <= 0x000f_ffff_ffff_f000u64);
                    assert(this.size > 0);
                }
            }

            valid_mem.push(prange);
        }

        Some(SevFWMetaData { cpuid_page, secrets_page, caa_page, valid_mem })
    } else {
        None
    }
}

#[inline]
pub fn flush_tlb_global_sync() {
    flush_tlb_broadcast(4 | 8, 0 , 0);
}

/// Broadcasts a TLB flush for a range of pages to ALL cores using hardware acceleration.
///
/// This replaces the need for IPI-based shootdowns for the specified range.
///
/// Use this function if you need to flush TLB entries across multiple CPUs efficiently.
#[verifier::external_body]
pub fn flush_tlb_broadcast(rax: u64, ecx: u32, edx: u16) {
    // EDX Layout for INVLPGB:
    // Bit 0:    VALID (Must be 1)
    // Bit 1:    GLOBAL (Flush global pages?)
    // Bits 2-?: Reserved
    // Bits 16-31: ASID (if not global)

    // EAX = Virtual Address or all
    // ECX = Page Count
    unsafe {
        core::arch::asm!(
            "invlpgb",
            in("rax") rax,
            in("ecx") ecx,
            in("edx") edx,
            options(nostack, preserves_flags)
        );

        core::arch::asm!("tlbsync", options(nostack, preserves_flags));
    }
}

/// Performs the launch of the guest firmware (OVMF).
#[verus_spec(
    requires
        igvm_params.wf(),
)]
pub fn launch_fw(
    igvm_params: &IgvmParams<'_>,
) {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_id = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id;
    let ghcb = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).ghcb;

    let vmsa_paddr = deko_rwlock_read_atomic_data! {
        PERCPU_AREAS,
        percpu_areas,
        __,
        {
            crate::check_shared_cpu_idx!(cpu_id as usize, percpu_areas, percpu_areas);

            let guest_vmsa = &percpu_areas.0[cpu_id as usize].guest_vmsa;

            deko_rwlock_read_atomic_data! {
                guest_vmsa,
                guest_vmsa,
                __,
                {
                    guest_vmsa.vmsa
                }
            }
        }
    };

    let Some(paddr) = vmsa_paddr else {
        die("No VMSA paddr found.");
    };

    kinfo!("The paddr of the VMSA is found at", paddr);

    proof_with!(Tracked(&cpu_perm) => Tracked(vmsa_perm));
    let vmsa = VMSA::this_vmsa(cpu);

    proof_with!(Tracked(&mut vmsa_perm));
    VMSA::populate_from_igvm_params(vmsa, igvm_params);

    let sev_features = vmsa.borrow(Tracked(&vmsa_perm)).sev_features;

    // We now register vmsa through ghcb.
    kinfo!("Registering the guest VMSA page. paddr => ", paddr);

    GuestHostCommunicationBlock::register_vmsa(ghcb, Tracked(cpu_perm.ghcb_perm), paddr, 0, 2, sev_features, 0);

    kinfo!("Finished registration");
}

/// Performs the necessary preparations for launching guest boot firmware.
///
/// This probes the IGVM parameters to locate the SEV firmware metadata
/// and try to make these pages as private to the guest.
#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>
    requires
        old(pgtable_perm).wf(),
        header.wf(),
        igvm_params.wf(),
        kernel_prange.wf(),
    ensures
        pgtable_perm.wf(),
        pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
        pgtable_perm.private_bit == old(pgtable_perm).private_bit,
        pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
        pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
)]
pub fn prepare_guest_fw(
    header: &DekoKernelLaunchInfo,
    igvm_params: &IgvmParams<'_>,
    kernel_prange: PaddrRange,
    cpuid_table: &CpuidTable,
) {
    // Many things to be done inside the function.
    if let Some(fw_meta) = get_sev_fw_metadata(igvm_params.igvm_param_block) {
        kdebug!("SEV FW Metadata found: ", fw_meta);

        // Now we need to make these pages accessible and mark them as valid in RMP.
        let mut memories = fw_meta.valid_mem.clone();
        if let Some(cpuid_page) = fw_meta.cpuid_page {
            memories.push(
                PaddrRange { start: cpuid_page, end: PhysAddr(cpuid_page.0 + PAGE_SIZE as u64) },
            );
        }
        if let Some(secrets_page) = fw_meta.secrets_page {
            memories.push(
                PaddrRange {
                    start: secrets_page,
                    end: PhysAddr(secrets_page.0 + PAGE_SIZE as u64),
                },
            );
        }
        if let Some(caa_page) = fw_meta.caa_page {
            memories.push(
                PaddrRange { start: caa_page, end: PhysAddr(caa_page.0 + PAGE_SIZE as u64) },
            );
        }
        proof_with!(Tracked(pgtable_perm));
        validate_fw_memories(header, igvm_params, &memories);

        init_guest_mmap(igvm_params);

        // BUG: Somebody overwrites the secrets/cpuid page so
        // that vmpl_switch fails due to invalid values read
        // on these pages.

        // copy the ACPI table into the fw so that
        // the guest fw can use it.
        copy_apci_tables_to_fw(&fw_meta, kernel_prange.clone(), cpuid_table);

        check_before_launch(&fw_meta);
        // Copy secrets page and caa page to fw.
        // validate fw.
        proof_with!(Tracked(pgtable_perm));
        validate_fw(igvm_params, kernel_prange);
        // prepare the fw launch (caa initialization.).
        prepare_fw_launch(&fw_meta);
    }
}

#[verus_spec(
    requires
        fw_meta.wf(),
)]
fn prepare_fw_launch(
    fw_meta: &SevFWMetaData,
) {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpuid = cpu.borrow(Tracked(&cpu_perm.ptr_perm)).cpu_id;

    if let Some(caa) = fw_meta.caa_page {
        deko_rwlock_read_atomic_data! {
            PERCPU_AREAS,
            percpu_areas,
            percpu_areas_perm,
            {
                let Some(ref percpu_areas) = percpu_areas else {
                    die("PERCPU_AREAS is not initialized");
                };

                kpanic_if!(
                    cpuid as usize >= percpu_areas.0.len(),
                    "CPU ID out of bounds for PERCPU_AREAS",
                    cpuid,
                );

                let cpu_shared = get_unchecked(&percpu_areas.0, cpuid as usize);

                deko_rwlock_write_atomic_data! {
                    cpu_shared.guest_vmsa,
                    guest_vmsa,
                    guest_vmsa_perm,
                    {
                        guest_vmsa.generation = guest_vmsa.generation.saturating_add(1);
                        guest_vmsa.gen_in_use = 0;
                        guest_vmsa.caa = Some(caa);
                    }
                }
            }
        }
    }

    // Allocate new VMSA for this CPU and then
    // update the guest mappings.
    DekoCpuCtx::allocate_guest_vmsa(cpu, Tracked(&mut cpu_perm));
    let _ = DekoCpuCtx::update_guest_vmsa(cpu, Tracked(cpu_perm));
}

#[verifier::external_body]
fn check_before_launch(
    fw_meta: &SevFWMetaData,
) {
    let Some(temp_mapping) = TempMapping::new(create_paddr_range(
        fw_meta.cpuid_page.unwrap(),
        1,
    )) else {
        kerror!("Failed to create temporary mapping for Secrets page check");
        die("");
    };

    let secrets_page = unsafe {  &*(temp_mapping.inner.start.0 as *const CpuidTable) };

    kdebug!("SEV FW Metadata: cpu page before launch: ", secrets_page);
}

/// Copies the CPUID page to the SEV firmware metadata location.
///
/// This method is necessary as guest boot firmware expects the CPUID page
/// to be located at a specific physical address provided in the SEV firmware
/// metadata.
#[verus_spec(
    requires
        fw_meta.wf(),
        kernel_region.wf(),
)]
fn copy_apci_tables_to_fw(
    fw_meta: &SevFWMetaData,
    kernel_region: PaddrRange,
    cpuid_table: &CpuidTable,
) {
    if let Some(cpuid) = fw_meta.cpuid_page {
        kinfo!("Copying CPUID page to firmware location at", cpuid);

        // Create a temporary mapping.
        let Some(cpuid_mapping) = TempMapping::new(cpuid..PhysAddr(cpuid.0 + PAGE_SIZE)) else {
            kerror!("Failed to create temporary mapping for CPUID page copy");
            die("");
        };

        do_copy_cpuid_to_fw(cpuid_table, cpuid_mapping);
    }

    kpanic_if!(fw_meta.caa_page.is_none(), "SEV FW Metadata: CAA page is required for ACPI table copy");
    kpanic_if!(fw_meta.secrets_page.is_none(), "SEV FW Metadata: Secrets page is required for ACPI table copy");

    let caa_page = fw_meta.caa_page.unwrap();
    let secrets_page = fw_meta.secrets_page.unwrap();

    copy_secrets_page_to_fw(secrets_page, caa_page, kernel_region);
}

#[verus_spec(
    requires
        kernel_region.wf(),
        secrets_page@ <= 0x8000_0000,
        secrets_page@ % PAGE_SIZE == 0,
        caa_page@ % PAGE_SIZE == 0,
)]
fn copy_secrets_page_to_fw(secrets_page: PhysAddr, caa_page: PhysAddr, kernel_region: PaddrRange) {
    kinfo!("Copying Secrets page to firmware location at", secrets_page);
    kinfo!("Copying CAA page to firmware location at", caa_page);

    let Some(temp_mapping) = TempMapping::new(create_paddr_range(secrets_page, 1)) else {
        kerror!("Failed to create temporary mapping for Secrets page copy");
        die("");
    };

    let lock = SECRETS_PAGE.acquire_read();
    let secrets_page_data = &lock.borrow().data;

    // SAFETY: We have ensured that the temporary mapping is valid.
    unsafe {
        do_modify_fw_secrets_page(&secrets_page_data, temp_mapping, kernel_region, caa_page);
    }

    lock.release_read();
}

/// This modifies the target secret page in place to avoid stack overflow.
///
/// As this requires raw pointer dereferencing, we mark this as `external_body`.
///
/// # Safety
///
/// This function performs raw pointer dereferencing and modifies memory directly.
/// The caller must ensure that the provided pointers are valid and point to
/// appropriate memory regions. However, since the input param is `&SecretsPage`
/// and a temporary mapping, this is safe.
#[verifier::external_body]
#[verus_spec(
    // with
        // something
    requires
        src.wf(),
        to.wf(),
        kernel_region.wf(),
        caa_page.wf(),
        to.inner.start@ % PAGE_SIZE == 0,
        to.inner.end@ - to.inner.start@ >= PAGE_SIZE as int,
        caa_page@ % PAGE_SIZE == 0,
        // TODO: Mapped.
)]
unsafe fn do_modify_fw_secrets_page(
    src: &SecretsPage,
    to: TempMapping,
    kernel_region: PaddrRange,
    caa_page: PhysAddr,
) {
    // Zero out the secrets page first.
    core::ptr::write_bytes(to.inner.start.0 as *mut u8, 0, PAGE_SIZE as usize);
    // Copy the secrets page data.
    core::ptr::copy(
        src as *const SecretsPage,
        to.inner.start.0 as *mut SecretsPage,
        1,
    );

    {
        // Zero out caa
        let temp_mapping = TempMapping::new(create_paddr_range(caa_page, 1)).expect("Failed to create temporary mapping for CAA page copy");
        // Now empty caa.
        core::ptr::write_bytes(temp_mapping.inner.start.0 as *mut u8, 0, PAGE_SIZE as usize);
    }

    // Then set up the necessary fields.
    let secrets_page = &mut *(to.inner.start.0 as *mut SecretsPage);

    secrets_page.vmpck[0] = [0u8;VMPCK_SIZE];
    secrets_page.vmpck[1] = [0u8;VMPCK_SIZE];
    // secrets_page.vmpck[2] = [0u8;VMPCK_SIZE];
    // secrets_page.vmpck[3] = [0u8;VMPCK_SIZE];
    secrets_page.svsm_base = kernel_region.start.0;
    secrets_page.svsm_size = (kernel_region.end.0 - kernel_region.start.0) as u64;
    secrets_page.svsm_caa = caa_page.0;
    secrets_page.svsm_max_version = 1;
    secrets_page.svsm_guest_vmpl = 2;  // guest == 2.
}

/// This functon validates the prevalidated memory regions specified
/// in the SEV firmware metadata.
#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
    requires
        old(pgtable_perm).wf(),
        header.wf(),
        igvm_params.wf(),
        forall|i: int|
            #![trigger memories@[i]]
            0 <= i < memories@.len() ==> {
                &&& memories@[i].wf()
                &&& memories@[i].start@ % PAGE_SIZE == 0
                &&& memories@[i].end@ % PAGE_SIZE == 0
            },
    ensures
        pgtable_perm.wf(),
        pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
        pgtable_perm.private_bit == old(pgtable_perm).private_bit,
        pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
        pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
)]
pub(crate) fn validate_fw_memories(
    header: &DekoKernelLaunchInfo,
    igvm_params: &IgvmParams<'_>,
    memories: &[PaddrRange],
) {
    // The lowest bit indicates if we are in shared or private mode.
    let need_page_change = igvm_params.igvm_param_page.environment_info & 0x1 != 0;

    kinfo!("Validating", memories.len(), "firmware memory regions");

    if !memories.is_empty() {
        for i in 0..memories.len()
            invariant
                i <= memories.len(),
                header.wf(),
                igvm_params.wf(),
                forall|j: int|
                    #![trigger memories@[j]]
                    0 <= j < memories@.len() ==> {
                        &&& memories@[j].wf()
                        &&& memories@[j].start@ % PAGE_SIZE == 0
                        &&& memories@[j].end@ % PAGE_SIZE == 0
                    },
                pgtable_perm.wf(),
                pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
                pgtable_perm.private_bit == old(pgtable_perm).private_bit,
                pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
                pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
        {
            let this = &memories[i];

            kinfo!("    Validating firmware memory region:", this);

            // Consultb the GHCB for page state change.
            if need_page_change {
                let (ghcb, Tracked(perm)) = current_ghcb();
                GuestHostCommunicationBlock::pstate_change(
                    ghcb,
                    Tracked(perm),
                    this.clone(),
                    PageStateChangeOp::Private,
                );

                kdebug!("Performed page state change to Private for firmware memory region:", this);
            }
            proof_with!(Tracked(pgtable_perm));
            validate_fw_memory_region(this.clone());
        }
    }
}

/// Validates a single memory region in the RMP table.
#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
    requires
        old(pgtable_perm).wf(),
        prange.wf(),
        prange.start@ % PAGE_SIZE == 0,
        prange.end@ % PAGE_SIZE == 0,
    ensures
        pgtable_perm.wf(),
        pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
        pgtable_perm.private_bit == old(pgtable_perm).private_bit,
        pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
        pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
)]
fn validate_fw_memory_region(prange: PaddrRange) {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    let mut cur = prange.start.0;
    let end = prange.end.0;

    while cur < end
        invariant
            prange.start@ <= cur <= end,
            prange.wf(),
            prange.start@ % PAGE_SIZE == 0,
            prange.end@ % PAGE_SIZE == 0,
            end == prange.end@,
            cur % PAGE_SIZE == 0,
            PAGE_SIZE == 0x1000,
            pgtable_perm.wf(),
            pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
            pgtable_perm.private_bit == old(pgtable_perm).private_bit,
            pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
            pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
        decreases end - cur,
    {
        // Create a temporary mapping for the physical address.
        let Some(temp_mapping) = TempMapping::new(
            create_paddr_range(PhysAddr(cur), 1),
        ) else {
            kerror!("Failed to create temporary mapping for firmware memory validation at", PhysAddr(cur));
            die("");
        };

        let flags = RmpFlags::rwx_guest_vmpl2();

        proof {
            assert(flags.bits() & Rmp_ALL_BITS == flags.bits()) by {
                bit_u32_and_auto();
            }
            assume(pgtable_perm.mapped(temp_mapping.inner.start));
        }

        // Then map these vaddrs into these paddrs.
        let (r, changed) = pvalidate(temp_mapping.inner.start.0, PAGE_SIZE, true, Tracked(pgtable_perm));
        kpanic_if!(r != 0, "PVALIDATE failed for firmware memory validation at", PhysAddr(cur), "with return code", r);
        kpanic_if!(!changed, "PVALIDATE CF indicates failure for firmware memory validation at", PhysAddr(cur), temp_mapping.inner,);

        let r = rmpadjust(temp_mapping.inner.start, PAGE_SIZE, flags, Tracked(pgtable_perm));
        kpanic_if!(r != 0, "RMPADJUST failed for firmware memory validation at", PhysAddr(cur), "with return code", r);

        zero_page(temp_mapping.inner.start, 1);

        cur += PAGE_SIZE;
    }
}

/// This function validates the Firmware's content but not its memory.
#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&mut PageTablePermission>,
    requires
        old(pgtable_perm).wf(),
        igvm_params.wf(),
        kernel_region.wf(),
    ensures
        pgtable_perm.wf(),
        pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
        pgtable_perm.private_bit == old(pgtable_perm).private_bit,
        pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
        pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
)]
#[verifier::external_body]
fn validate_fw(igvm_params: &IgvmParams<'_>, kernel_region: PaddrRange) {
    broadcast use RmpFlags::lemma_each_bit_is_valid;

    let fw_flash: alloc::vec::Vec<Range<PhysAddr>, crate::mm::frame_allocator::DekoAllocatorApi> = get_fw_regions_from_igvm(igvm_params);
    // I'm being lazy here: we need to check OVMF:
    // Flash range is 3GiB-4GiB and one ends at 4GiB (0x100_000_000)

    for i in 0..fw_flash.len()
        invariant
            i <= fw_flash.len(),
            igvm_params.wf(),
            kernel_region.wf(),
            forall|j: int|
                #![trigger fw_flash@[j]]
                0 <= j < fw_flash@.len() ==> {
                    &&& fw_flash@[j].wf()
                    &&& fw_flash@[j].start@ % PAGE_SIZE == 0
                    &&& fw_flash@[j].end@ % PAGE_SIZE == 0
                    &&& fw_flash@[j].end@ < 0x000f_ffff_ffff_f000u64
                },
            pgtable_perm.wf(),
            pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
            pgtable_perm.private_bit == old(pgtable_perm).private_bit,
            pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
            pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
    {
        let this = &fw_flash[i];
        let nr_pages = (this.end.0 - this.start.0) / PAGE_SIZE as u64;
        kinfo!("Flash region", i, ":", this, "nr_pages =", nr_pages => hex);

        for i in 0..nr_pages as usize
            invariant
                nr_pages as int == (this.end.0 - this.start.0) / PAGE_SIZE as int,
                i <= nr_pages as usize,
                this.wf(),
                this.start@ % PAGE_SIZE == 0,
                this.end@ % PAGE_SIZE == 0,
                this.end@ < 0x000f_ffff_ffff_f000u64,
                this.end@ == nr_pages * PAGE_SIZE + this.start@,
                igvm_params.wf(),
                kernel_region.wf(),
                PAGE_SIZE == 0x1000,
                pgtable_perm.wf(),
                pgtable_perm.mapping_space == old(pgtable_perm).mapping_space,
                pgtable_perm.private_bit == old(pgtable_perm).private_bit,
                pgtable_perm.shared_bit == old(pgtable_perm).shared_bit,
                pgtable_perm.pgtable_perm == old(pgtable_perm).pgtable_perm,
        {
            let cur = i as u64 * PAGE_SIZE + this.start.0;
            proof {
                assert(cur % PAGE_SIZE == 0) by {
                    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                        i as int,
                        this.start@ as int,
                        PAGE_SIZE as int,
                    );
                }
                assert(cur <= this.end@);
            }

            let Some(temp_mapping) = TempMapping::new(create_paddr_range(PhysAddr(cur), 1)) else {
                kerror!("Failed to create temporary mapping for firmware validation");
                die("");
            };

            let rmp_flags = RmpFlags::rwx_guest_vmpl2();

            proof {
                assert(rmp_flags.bits() & Rmp_ALL_BITS == rmp_flags.bits()) by {
                    bit_u32_and_auto();
                }

                // Note this proof should comes from the precondition of
                // deko_main that all fw memory regions are mapped on this
                // cpu; I'm thinking about how to express this in a better way.
                // Perhaps we will need a more high-level spec function to
                // describe that regions are mapped in the page table; then
                // we check if the given region is a subregion of these mapped regions.
                // and if so we can conclude that each page in the region is mapped.
                assume(pgtable_perm.mapped(temp_mapping.inner.start));
            }

            // Now we can validate the page at `cur`.
            ktrace!("Validating firmware page at", temp_mapping.inner.start, "for firmware physical address", PhysAddr(cur));
            let r = rmpadjust(temp_mapping.inner.start, PAGE_SIZE, rmp_flags, Tracked(pgtable_perm));

            // Panics the system since firmware validation failure is fatal.
            kpanic_if!(r != 0, "RMPADJUST failed for firmware validation at", VirtAddr(cur), "with return code", r);
        }
    }
}

#[inline]
#[verus_spec(
    requires
        mm.wf(),
        mm.start@ % PAGE_SIZE == 0,
        mm.end@ % PAGE_SIZE == 0,
)]
pub fn page_state_change(mm: PaddrRange, op: PageStateChangeOp) {
    let (ghcb, Tracked(perm)) = current_ghcb();
    GuestHostCommunicationBlock::pstate_change(ghcb, Tracked(perm), mm, op);
}

#[inline]
#[verus_spec(
    requires
        vmpl <= 3,
)]
pub fn vmpl_run(vmpl: u32) {
    let (ghcb, Tracked(perm)) = current_ghcb();
    GuestHostCommunicationBlock::vmpl_run(ghcb, Tracked(perm), vmpl);
}

#[inline]
#[verifier::external_body]
#[verus_spec(
    requires
        to.wf(),
        to.inner.start@ % PAGE_SIZE == 0,
)]
fn do_copy_cpuid_to_fw(cpuid_table: &CpuidTable, to: TempMapping) {
    unsafe {
        core::ptr::copy_nonoverlapping(cpuid_table as _, to.inner.start.0 as *mut CpuidTable, 1);
    }

    let fw_cpuid_table = unsafe { &mut *(to.inner.start.0 as *mut CpuidTable) };
    kdebug!("Copied CPU ID table to firmware location at", to.inner.start, ": ", fw_cpuid_table);
}

/// When a guest receives a #HV notification at any time, guest may choose
/// to acknowledge it immediately or to defer it until it enables interrupts.
///
/// Interrupt re-enabling code paths need to explicitly check for pending #HVs.
#[inline]
#[verifier::exec_allows_no_decreases_clause]
pub fn after_irq_enable() {
    doorbell::process_pending_hv_events();
}

/// # HV is delivered without regard to interrupt shadows, so chances are high
/// that the guest will lose the ability to control interaction between HLT and
/// interrupts.
///
/// This code is a guard to ensure that guest can properly suspend when no interrupts
/// are pending while also ensuring that a guest will neither miss pending interrupts
/// or suspend forever and become "ghost".
#[inline]
#[verifier::external_body]
pub fn idle_halt(doorbell: u64) {
    unsafe {
        // let info = core::slice::from_raw_parts(doorbell as *const u8, core::mem::size_of::<doorbell::HVDoorbell>());

        // // kdebug!("Entering idle halt with doorbell info:", info);

        __snp_idle_halt(doorbell as *const doorbell::HVDoorbell)
    }
}

}

} // verus!
