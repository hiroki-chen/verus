use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn read_msr(msr: u32) -> u64 {
    let low: u32;
    let high: u32;
    unsafe {
        core::arch::asm!("rdmsr",
                in("ecx") msr,
                out("eax") low,
                out("edx") high,
            );
    }

    ((high as u64) << 32) | (low as u64)
}

#[verifier::external_body]
pub fn write_msr(msr: u32, value: u64) {
    let low: u32 = value as u32;
    let high: u32 = (value >> 32) as u32;
    unsafe {
        core::arch::asm!("wrmsr",
                in("ecx") msr,
                in("eax") low,
                in("edx") high,
            );
    }
}

} // verus!
