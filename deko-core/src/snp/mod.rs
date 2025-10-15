use core::sync::atomic::AtomicU32;

use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::ctx::DekoCtxPermission;
use crate::hal::{PlatformApi, PlatformType};
use crate::mm::paging::PteFlags;
use crate::mm::{
    PageEncryptionMasks, FEATURE_MASK, MAX_PHYS_ADDR, PHYS_ADDR_SIZE, PTE_MASK_PRIVATE,
    PTE_MASK_SHARED,
};

pub mod ghcb;
pub mod snpcall;

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

pub struct Snp;

impl Snp {
    #[inline(always)]
    fn get_page_encryption_masks(&self) -> PageEncryptionMasks {
        if has_vtom() {
            vstd::vpanic!("We do not support VTOM yet");
        } else {
            PageEncryptionMasks {
                private_pte_mask: 1 << 51,
                shared_pte_mask: 0,
                addr_mask_width: 51,
                phys_addr_sizes: 48,  // todo: do not hardcode this.
            }
        }
    }
}

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }

    fn init_platform(&self, header: Stage2LaunchInfo) {
        // Set the top of the virtual memory.
        let vtom = header.vtom as usize;
        SNP_VTOM.init(vtom);

        // Set the encryption bit.
        let masks = self.get_page_encryption_masks();
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
    fn validate_memory(
        &self,
        Tracked(ctx_perm): Tracked<&mut DekoCtxPermission>,
        heap_start: u64,
        heap_end: u64,
    ) -> (r: bool)
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
                self.wf(),
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

            let (ret, cf) = Self::pvalidate(addr.0, 0x1000, true, Tracked(ctx_perm));
            cur += 0x1000;
        }

        true
    }
}

impl WellFormed for Snp {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
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
