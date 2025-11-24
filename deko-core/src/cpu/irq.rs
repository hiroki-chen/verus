use vstd::prelude::*;

verus! {

/// Disable the CPU interrupts unconditionally.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
        // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
pub fn irq_disable() {
    unsafe {
        core::arch::asm!("cli", options(nomem, nostack, preserves_flags));
    }
}

/// Enable the CPU interrupts unconditionally.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
pub fn irq_enable() {
    unsafe {
        core::arch::asm!("sti", options(nomem, nostack, preserves_flags));
    }
}

/// Check if the the CPU interrupts are enabled.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with
        // Tracked(core): Tracked<DekoCPUCore>,
)]
pub fn irq_enabled() -> bool {
    let rflags: usize;
    unsafe {
        core::arch::asm!(
            "pushfq",
            "pop {}",
            out(reg) rflags,
            options(nomem, att_syntax, preserves_flags)
        );
    }

    (rflags & (1 << 9)) != 0
}

} // verus!
