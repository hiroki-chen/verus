use core::sync::atomic::{AtomicBool, Ordering};

use deko_macros::DekoDebug;
use deko_std::address::VirtAddr;
use deko_std::bits::bit_u64_and_auto;
use vstd::prelude::*;

use super::regs::{self, read_cr4, write_cr4, Cr4Flags};

verus! {

/// Indicates whether we are to flush TLBs on all CPUs.
exec static FLUSH_SMP: AtomicBool = AtomicBool::new(false);

#[derive(DekoDebug, PartialEq, Eq, Clone, Copy)]
pub enum TlbFlushMode {
    /// Flush aLL.
    AllGlobal,
    /// Flush private part.
    AllNonGlobal,
}

#[verus_verify]
impl TlbFlushMode {
    pub fn flush_percpu(&self) {
        match self {
            Self::AllGlobal => flush_tlb_global_percpu(),
            Self::AllNonGlobal => flush_tlb_percpu(),
        }
    }

    pub fn flush_all(&self) {
        // If SMP has not yet been started, then perform all flushes as local only.
        // Prior to SMP startup, there is no need to reach into other processors,
        // and the SVSM platform object may not even exist when flushes are
        // attempted prior to SMP startup.
        if FLUSH_SMP.load(Ordering::Relaxed) {
            // Here we do not use IPIs.
            crate::imp::flush_tlb_global_sync();
        } else {
            self.flush_percpu();
        }
    }
}

#[inline]
#[verifier::external_body]
pub fn flush_tlb_percpu() {
    // SAFETY: reloading CR3 with its current value is always safe.
    unsafe {
        core::arch::asm!(
            "
            movq %cr3, %rax
            movq %rax, %cr3
            ",
             out("rax") _,
             options(att_syntax));
    }
}

/// Flushes all TLB entries on the **current CPU**, including those marked with the Global (G) bit.
///
/// This works by toggling the `CR4.PGE` (Page Global Enable) bit. This forces the CPU
/// to invalidate all cached translations, including kernel mappings that normally
/// persist across CR3 context switches.
///
/// # SMP Safety
/// **This operation is local.** It does not affect other cores.
/// If you updated a shared page table (like the per-cpu area mappings), you must ensure
/// this function is executed on **every active CPU** (e.g., via an IPI broadcast)
/// to prevent stale translations on other cores.
pub fn flush_tlb_global_percpu() {
    broadcast use Cr4Flags::lemma_each_bit_is_valid;

    let old_cr4 = read_cr4();

    let cr4 = Cr4Flags::from_bits_truncate(old_cr4.bits() ^ regs::PGE);

    proof {
        assert(cr4.bits() & regs::Cr4_ALL_BITS == cr4.bits()) by {
            bit_u64_and_auto();
        }
    }

    write_cr4(cr4);
    write_cr4(old_cr4);
}

#[inline]
pub fn set_tlb_flush_smp() {
    FLUSH_SMP.store(true, Ordering::Relaxed);
}

#[inline]
#[verifier::external_body]
pub fn flush_address_percpu(va: VirtAddr) {
    // SAFETY: Inline assembly to invalidate TLB Entries, which does not change
    // any state related to memory safety.
    unsafe {
        core::arch::asm!("
             invlpg (%rax)",
             in("rax") va.0,
             options(att_syntax));
    }
}

#[inline]
pub fn flush_tlb_global_sync() {
    TlbFlushMode::AllGlobal.flush_all();
}

} // verus!
