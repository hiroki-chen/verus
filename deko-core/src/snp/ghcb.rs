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
use deko_std::snp::ghcb::{
    GuestHostCommucationBlock, SNP_REG_GHCB_GPA_REQ, SNP_REG_GHCB_GPA_RESP, SNP_STATE_CHANGE_REQ,
    SNP_STATE_CHANGE_RESP,
};
use deko_std::sync::RwLockToks::reader;
use vstd::atomic::PAtomicU8;
use vstd::prelude::*;

use crate::cpu::{DekoCpuCtx, DekoCpuCtxPermission};
use crate::mm::paging::{PageTable, PteFlags};
use crate::mm::virt_to_phys;

verus! {

/// Validates the GHCB page allocated for the current CPU core.
#[verifier::external_body]
pub fn validate_ghcb(
    ctx: DekoPPtr<DekoCpuCtx>,
    Tracked(ctx_perm): Tracked<&mut DekoCpuCtxPermission>,
)
    requires
        old(ctx_perm).wf_with(ctx),
        old(ctx_perm).ghcb_perm.wf(),
    ensures
        ctx_perm.wf_with(ctx),
{
    let ctx = ctx.borrow(Tracked(&ctx_perm.ptr_perm));
    let pgtable = ctx.pgtable();
    let ghcb = ctx.ghcb();
    let ms = ctx.kernel_mapping();
    let private_bit = ctx.private_bit();
    let shared_bit = ctx.shared_bit();

    let ghcb_vaddr = VirtAddr::new(ghcb.addr() as u64);
    // let ghcb_paddr = virt_to_phys(ghcb_vaddr); // todo: FIX ME.
    let ghcb_paddr = PhysAddr(ghcb.addr() as u64);
    // Invalidate this page from the CVM.
    crate::snp::Snp::pvalidate(ghcb_vaddr.0, 0x1000, false, Tracked::assume_new());
    // Notify the hypervisor that this page is now invalid.
    msr_set_page_valid(ghcb_paddr, false);

    // Then set the GHCB page as shared in the page table.
    PageTable::set_shared_4k(
        pgtable,
        Tracked(&mut ctx_perm.pgtable_perm),
        ghcb_vaddr,
        &ms,
        // private_bit,
        1 << 51,
        // shared_bit,
        1 << 0,
    );

    // Register the GHCB GPA with the hypervisor.
    msr_register_ghcb_gpa(ghcb_paddr);
}

pub fn msr_register_ghcb_gpa(paddr: PhysAddr)
    requires
        paddr.wf(),
{
    let mut addr = paddr.0;

    addr |= SNP_REG_GHCB_GPA_REQ;
    let response = no_irq_zone(
        ||
            {
                write_msr(MSR_AMD64_SEV_ES_GHCB, addr);
                raw_vmgexit();
                read_msr(MSR_AMD64_SEV_ES_GHCB)
            },
    );

    if response & 0xfff != SNP_REG_GHCB_GPA_RESP {
        vstd::vpanic!("Failed to register GHCB GPA via MSR");
    }
    if response & !(0xfff) != paddr.0 {
        vstd::vpanic!("Failed to register GHCB GPA via MSR");
    }
}

/// Set a page to be shared to tell the hypervisor to re-claim it.
pub fn msr_set_page_valid(paddr: PhysAddr, valid: bool)
    requires
        paddr.wf(),
{
    let mut addr = paddr.0 & 0x000f_ffff_ffff_f000u64;
    if valid {
        addr |= 1u64 << 52;
    } else {
        addr |= 2u64 << 52;
    }
    addr |= SNP_STATE_CHANGE_REQ;

    // Change of the state is critical so we do this in a no-irq zone.
    let response = no_irq_zone(
        ||
            {
                write_msr(MSR_AMD64_SEV_ES_GHCB, addr);
                raw_vmgexit();
                read_msr(MSR_AMD64_SEV_ES_GHCB)
            },
    );

    if response & 0xfff != SNP_STATE_CHANGE_RESP {
        vstd::vpanic!("Failed to change the page state via GHCB");
    }
    if response & !(0xfff) != 0 {
        vstd::vpanic!("Failed to change the page state via GHCB");
    }
}

/// Fetch the current GHCB structure for this specific CPU core.
pub fn current_ghcb() -> (r: (
    DekoPPtr<GuestHostCommucationBlock>,
    Tracked<DekoPointsTo<GuestHostCommucationBlock>>,
))
    ensures
        r.1@.wf(),
        r.1@.is_init(),
        r.1@.pptr() == r.0@,
{
    let (cpu, Tracked(perm)) = DekoCpuCtx::this_cpu();
    let cpu = cpu.borrow(Tracked(&perm.ptr_perm));

    // `this_cpu` is causing page fault so the mapping is problematic.
    (cpu.ghcb(), Tracked(perm.ghcb_perm))
}

} // verus!
