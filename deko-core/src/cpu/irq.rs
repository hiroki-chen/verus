use vstd::prelude::*;

verus! {

/// Enter a zone where interrupts are disabled.
#[verifier::external_body]
pub fn no_irq_zone<T>(f: impl FnOnce() -> T) -> T {
    unsafe {
        core::arch::asm!("cli");
    }
    let v = f();
    unsafe {
        core::arch::asm!("sti");
    }

    v
}

} // verus!
