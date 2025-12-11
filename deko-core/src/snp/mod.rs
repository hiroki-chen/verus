use core::ops::Range;
use core::sync::atomic::AtomicU32;

use deko_macros::{with_atomic_pred, DekoDebug};
use deko_std::prelude::*;
use vstd::cell::PCell;
use vstd::invariant;
use vstd::prelude::*;

use crate::cpu::apic::Apic;
use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::{
    DekoCpuCtx, DekoCpuCtxPermission, PerCpuAreas, PerCpuShared, CPUID_MAX_COUNT, CPU_AREA_MAGIC,
    PERCPU_AREAS,
};
use crate::mm::paging::{PageTablePermission, PteFlags};
use crate::mm::{
    phys_to_virt, virt_to_phys, PageEncryptionMasks, DEKO_FRAME_ALLOCATOR, FEATURE_MASK,
    MAX_PHYS_ADDR, PHYS_ADDR_SIZE, PTE_MASK_PRIVATE, PTE_MASK_SHARED,
};
use crate::snp::ghcb::{current_ghcb, msr_register_ghcb_gpa, GuestHostCommucationBlock};
use crate::{kinfo, Stage2LaunchInfo};

pub mod ghcb;
pub mod logging;
pub mod req;

extern "C" {
    /// A global flag to indicate whether the AP has been started.
    static mut ap_flag: AtomicU32;
}

verus! {

pub const VMPCK_SIZE: usize = 32;

pub const VMPL_MAX: usize = 4;

pub exec static SECRETS_PAGE: DekoRwLock<SecretsPage, SecretsPagePermission, SecretsPagePred>
    ensures
        SECRETS_PAGE.wf(),
{
    let r = DekoRwLock::new(
        DekoAtomicData::new_with(SecretsPage::new(), Tracked(SecretsPagePermission {  })),
        (),
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
    #[deko(skip)]
    reserved_00c: u32,
    gosvw: [u8; 16],
    vmpck: [[u8; VMPCK_SIZE]; VMPL_MAX],
    #[deko(skip)]
    reserved_0a0: [u8; 96],
    vmsa_tweak_bmp: [u64; 8],
    svsm_base: u64,
    svsm_size: u64,
    svsm_caa: u64,
    svsm_max_version: u32,
    svsm_guest_vmpl: u8,
    reserved_15d: [u8; 3],
    tsc_factor: u32,
    #[deko(skip)]
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
            old(self).wf(),
            from.wf(),
        ensures
            self.wf(),
    )]
    pub fn copy_from(&mut self, from: VirtAddr) {
        unsafe {
            core::ptr::copy_nonoverlapping(
                from.0 as *const SecretsPage,
                self as *mut SecretsPage,
                1,
            );
        }
    }
}

#[verus_spec(
    with
        Tracked(pgtable_perm): Tracked<&PageTablePermission>
    requires
        pgtable_perm.mapped(from),
        from.wf(),
)]
pub fn secrets_page_init(from: VirtAddr) {
    let (DekoAtomicData { mut data, perm }, handle) = SECRETS_PAGE.acquire_write();

    proof_with!(Tracked(pgtable_perm));
    data.copy_from(from);
    handle.release_write(DekoAtomicData { data, perm });
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
    kinfo!("IGVM Parameters\n\t", igvm_params);
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
    let shared_area_ptr = {
        let read_handle = PERCPU_AREAS.acquire_read();
        // The permission is discarded; you can only obtain this permission
        // if you own this.
        let (ptr, _) = read_handle.borrow().data.0.index_as_ptr(0);

        read_handle.release_read();

        ptr
    };

    // 1. First we set up the GHCB page for this CPU.
    // Get the page table from the context that was passed in
    let bsp_pgtable = ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).pgtable;
    let tracked bsp_pgtable_perm = &ctx_perm.pgtable_perm;
    let (ghcb, Tracked(ghcb_perm)) = Box::<GuestHostCommucationBlock>::new_zeroed(
        &DEKO_FRAME_ALLOCATOR.0,
    );
    let (ghcb, Tracked(ghcb_perm)) = ghcb.into_ptr(Tracked(ghcb_perm));

    // 2. We now set up the percpu area for this CPU.
    // Note that we do not need to initialize the percpu area since it is
    // zeroed out by Box::new_zeroed.
    // We just need to set up the page table entry and the CpuData struct.
    let (bsp_percpu, Tracked(bsp_percpu_perm)) = Box::new_zeroed(&DEKO_FRAME_ALLOCATOR.0);
    let bsp_percpu_paddr = PhysAddr(bsp_percpu.addr() as u64);
    let (bsp_percpu_ptr, Tracked(mut bsp_percpu_perm)) = bsp_percpu.into_ptr(
        Tracked(bsp_percpu_perm),
    );

    // 3. Initialize the percpu area.
    // Get the platform-specific PTE mask values for this CPU
    let masks = get_page_encryption_masks();

    // Use the existing context that was passed in from setup_env
    // This context already has the proper stage2_launch_info and other components
    let bsp_percpu = DekoCpuCtx::new(
        bsp_pgtable,
        shared_area_ptr,
        ghcb,
        0,  // cpu_id
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).shared_bit,
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).private_bit,
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).mapping_space,
        None,  // vm_region
        None,  // ctx_switch_stack
        None,  // ist_stack
        None,
    );
    bsp_percpu_ptr.write(Tracked(&mut bsp_percpu_perm), bsp_percpu);

    let tracked mut cpu_ctx_perm = DekoCpuCtxPermission {
        ptr_perm: bsp_percpu_perm,
        pgtable_perm: ctx_perm.pgtable_perm,
        ghcb_perm,
        vm_region_perm: None,
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
pub fn validate_vaddr_region(vrange: Range<VirtAddr>, validate: bool) {
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
        pvalidate(cur, PAGE_SIZE, validate, Tracked(&mut ctx_perm.pgtable_perm));
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
        pgtable_perm.wf(),
        // old(pgtable_perm).private_bit() == pgtable_perm.private_bit(),
        // old(pgtable_perm).shared_bit() == pgtable_perm.shared_bit(),
        old(pgtable_perm) == pgtable_perm,
{
    let rax = vaddr;
    let ret: u64;
    let rcx = if psize == PAGE_SIZE {
        RMP_4K
    } else {
        RMP_2M
    };
    let cf: u64;
    let rdx = if validate {
        1
    } else {
        0
    };

    unsafe {
        core::arch::asm!(
            "xorq %r8, %r8",
            "pvalidate",
            "adcq %r8, %r8",
            in("rax")  rax,
            in("rcx")  rcx,
            in("rdx")  rdx,
            lateout("rax") ret,
            lateout("r8") cf,
            options(att_syntax));
    }

    (ret, cf == 0)
}

#[verifier::external_body]
pub fn rmpadjust(vaddr: u64, psize: u64, Tracked(perm): Tracked<&mut DekoCtxPermission>) -> (ret:
    u64)
    requires
        old(perm).wf(),
    ensures
        perm.wf(),
        old(perm).deko_ctx_ptr_perm.pptr()
            === perm.deko_ctx_ptr_perm.pptr(),
// todo: old(perm).rmpadjust_spec == perm.

{
    let ret: u64;

    unsafe {
        core::arch::asm!(
            ".byte 0xf3,0x0f,0x01,0xf1",
            in("rax") vaddr, in("rcx") psize,
            lateout("rax") ret,
            options(nostack)
        );
    }

    ret
}

pub fn rdmsr(msr: u32) -> u64 {
    let (ghcb, Tracked(perm)) = current_ghcb();

    let (high, low, _) = GuestHostCommucationBlock::rdmsr(ghcb, Tracked(perm), msr);

    ((high as u64) << 32) | (low as u64)
}

pub fn wrmsr(msr: u32, value: u64) {
    let (ghcb, Tracked(perm)) = current_ghcb();

    let low = (value & 0xffff_ffff) as u32;
    let high = (value >> 32) as u32;

    GuestHostCommucationBlock::wrmsr(ghcb, Tracked(perm), msr, high, low);
}

/// Sets up the local APIC for the current CPU.
pub fn setup_apic(ctx: DekoPPtr<DekoCpuCtx>, Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>)
    requires
        old(ctx_perm).wf_with(ctx),
    ensures
        ctx_perm.wf_with(ctx),
{
    let apic = ctx.borrow(Tracked(&ctx_perm.ptr_perm)).apic();

    // Enable x2APIC mode
    apic.enable();
}

} // verus!
deko_bitflags! {
    pub struct SnpStatus: u32 {
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
        const VMSA_REG_PROT = 12;
        const SMT_PROT = 13;
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
    {
        let bits = read_msr(MSR_SEV_STATUS) as u32;

        SnpStatusFlags { bits, flags: Ghost(Self::from_bits(bits)) }
    }
}

} // verus!
