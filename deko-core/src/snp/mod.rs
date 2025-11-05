use core::sync::atomic::AtomicU32;

use deko_std::prelude::*;
use deko_std::snp::ghcb::GuestHostCommucationBlock;
use vstd::cell::PCell;
use vstd::prelude::*;

use crate::cpu::ctx::{DekoCtx, DekoCtxPermission};
use crate::cpu::{
    DekoCpuCtx, DekoCpuCtxPermission, PerCpuAreas, PerCpuShared, CPUID_MAX_COUNT, CPU_AREA_MAGIC,
    PERCPU_AREAS,
};
use crate::logging::DekoDebug;
use crate::mm::paging::PteFlags;
use crate::mm::{
    phys_to_virt, virt_to_phys, PageEncryptionMasks, DEKO_FRAME_ALLOCATOR, FEATURE_MASK,
    MAX_PHYS_ADDR, PHYS_ADDR_SIZE, PTE_MASK_PRIVATE, PTE_MASK_SHARED,
};
use crate::snp::ghcb::msr_register_ghcb_gpa;

pub mod ghcb;

pub(crate) mod logging;

extern "C" {
    /// A global flag to indicate whether the AP has been started.
    static mut ap_flag: AtomicU32;
}

verus! {

#[verifier::external_body]
#[inline(always)]
pub fn get_igvm_params<'a>(header: &'a Stage2LaunchInfo) -> (r: &'a IgvmParamBlock)
    requires
        header.wf(),
    ensures
        r.wf(),
{
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

pub exec static SNP_VTOM: OnceCellNoPred<usize>
    ensures
        SNP_VTOM.wf(),
{
    OnceCellNoPred::new(Ghost(()))
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
        heap_end > heap_start,
        heap_start % 0x1000 == 0,
        heap_end % 0x1000 == 0,
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
            cur <= heap_end,
            ctx_perm.wf(),
            cur % 0x1000 == 0,
            heap_start % 0x1000 == 0,
            heap_end % 0x1000 == 0,
            heap_end <= LOWMEM_END as u64,
            old(ctx_perm).deko_ctx_ptr_perm.pptr() === ctx_perm.deko_ctx_ptr_perm.pptr(),
            old(ctx_perm).private_bit() == ctx_perm.private_bit(),
            old(ctx_perm).shared_bit() == ctx_perm.shared_bit(),
        decreases heap_end - cur,
    {
        // check if this address is aligned with 2MB page?
        let addr = VirtAddr::new(cur);

        proof {
            // Prove that the canonicalized address is also aligned to 4K.
            VirtAddr::lemma_make_canonical_preserves_alignment_4k(cur, addr@);
        }

        let (ret, cf) = pvalidate(addr.0, 0x1000, true, Tracked(ctx_perm));
        cur += 0x1000;
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
fn init_guest_host(ctx: DekoPPtr<DekoCpuCtx>, Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>)
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

    // Print the Deko banner with build information
    crate::logging::print_banner();

    // Print IGVM parameter information for debugging
    crate::logging::print_str("IGVM Parameters:\n");
    igvm_params.deko_debug();
    crate::logging::print_str("\n");
}

pub fn init_each_cpu(ctx: DekoPPtr<DekoCtx>, Tracked(ctx_perm): Tracked<DekoCtxPermission>) -> (r: (
    DekoPPtr<DekoCpuCtx>,
    Tracked<DekoCpuCtxPermission>,
))
    requires
        ctx_perm.wf_with(ctx),
    ensures
        r.1@.wf_with(r.0),
{
    let shared_area_ptr = {
        let read_handle = PERCPU_AREAS.acquire_read();
        // The permission is discarded; you can only obtain this permission
        // if you own this.
        let (ptr, _) = read_handle.borrow().0.index_as_ptr(0);

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
        masks.shared_pte_mask,
        masks.private_pte_mask,
        ctx.borrow(Tracked(&ctx_perm.deko_ctx_ptr_perm)).mapping_space,
    );
    bsp_percpu_ptr.write(Tracked(&mut bsp_percpu_perm), bsp_percpu);

    let tracked mut cpu_ctx_perm = DekoCpuCtxPermission {
        ptr_perm: bsp_percpu_perm,
        pgtable_perm: ctx_perm.pgtable_perm,
        ghcb_perm,
    };

    // TODO: CONSTRUCT THE PAIR.
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
    Tracked(perm): Tracked<&mut DekoCtxPermission>,
) -> (r: (u64, bool))
    requires
        psize == 0x1000 || psize == 0x200000,  // Either 4K or 2M page.
        vaddr % 0x1000 == 0,
        old(perm).wf(),
    ensures
        perm.wf(),
        old(perm).deko_ctx_ptr_perm.pptr() === perm.deko_ctx_ptr_perm.pptr(),
        old(perm).private_bit() == perm.private_bit(),
        old(perm).shared_bit() == perm.shared_bit(),
{
    let rax = vaddr;
    let ret: u64;
    let rcx = if psize == 0x1000 {
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

        SnpStatusFlags { bits, flags: Ghost(from_bits(bits)) }
    }
}

} // verus!
