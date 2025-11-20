use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

deko_bitflags! {
    pub struct Cr0: u64 {
        const PE = 0; // Protection Enable
        const MP = 1; // Monitor Coprocessor
        const EM = 2; // Emulation
        const TS = 3; // Task Switched
        const ET = 4; // Extension Type
        const NE = 5; // Numeric Error
        const WP = 16; // Write Protect
        const AM = 18; // Alignment Mask
        const NW = 29; // Not Write-through
        const CD = 30; // Cache Disable
        const PG = 31; // Paging
    }
}

deko_bitflags! {
    pub struct Cr4: u64 {
        const VME = 0; // Virtual-8086 Mode Extensions
        const PSE = 4; // Page Size Extension
        const PAE = 5; // Physical Address Extension
        const PGE = 7; // Page Global Enable
        const OSFXSR = 9; // OS Support for FXSAVE and FXRSTOR instructions
        const OSXMMEXCPT = 10; // OS Support for Unmasked SIMD Floating-Point Exceptions
        const SMEP = 20; // Supervisor Mode Execution Protection
        const SMAP = 21; // Supervisor Mode Access Prevention
    }
}

/// Reads the current value of the CR0 register.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    ensures
        r.wf(),
        r.bits() & Cr0_ALL_BITS == r.bits(),
)]
pub fn read_cr0() -> Cr0Flags {
    let mut cr0: u64;

    unsafe {
        core::arch::asm!(
            "movq %cr0, {}",
            out(reg) cr0,
            options(att_syntax)
        );
    }

    Cr0Flags::from_bits_truncate(cr0)
}

/// Reads the current value of the CR4 register.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    ensures
        r.wf(),
        r.bits() & Cr4_ALL_BITS == r.bits(),
)]
pub fn read_cr4() -> Cr4Flags {
    let mut cr4: u64;

    unsafe {
        core::arch::asm!(
            "movq %cr4, {}",
            out(reg) cr4,
            options(att_syntax)
        );
    }

    Cr4Flags::from_bits_truncate(cr4)
}

/// Writes the given value to the CR4 register.
///
/// We ensure that the incoming bits are valid before writing to CR4.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    requires
        cr4.wf(),
        cr4.bits() & Cr4_ALL_BITS == cr4.bits(),
)]
pub fn write_cr4(cr4: Cr4Flags) {
    unsafe {
        core::arch::asm!(
            "movq {}, %cr4",
            in(reg) cr4.bits(),
            options(att_syntax),
        );
    }
}

/// Writes the given value to the CR0 register.
///
/// We ensure that the incoming bits are valid before writing to CR0.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    requires
        cr0.wf(),
        cr0.bits() & Cr0_ALL_BITS == cr0.bits(),
)]
pub fn write_cr0(cr0: Cr0Flags) {
    unsafe {
        core::arch::asm!(
            "movq {}, %cr0",
            in(reg) cr0.bits(),
            options(att_syntax),
        );
    }
}

/// This is an extremly unsafe function that loads the given value into CR3 register.
///
/// # Safety
///
/// This function is unsafe because loading an invalid value into CR3 can cause
/// the CPU to enter an undefined state, leading to system crashes or data corruption.
///
/// It is the caller's responsibility to ensure that the provided value is a valid
/// physical address of a properly configured page table.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    requires
        val.wf(),
        // val@ <= u32::MAX, ?? some region constraints.
    ensures
)]
#[no_mangle]
pub unsafe fn load_cr3(val: PhysAddr) {
    core::arch::asm!(
        "mov {}, %cr3; hlt",
        in(reg) val.0,
        options(att_syntax),
    );
}

/// Initializes the CR0 register.
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
pub fn cr0_init() {
    broadcast use Cr0Flags::lemma_each_bit_is_valid;
    broadcast use Cr0Flags::lemma_from_bits_single;

    let mut cr0 = read_cr0();
    let tracked old_cr0 = &cr0;
    cr0.remove(NW);
    cr0.remove(CD);
    cr0 = Cr0Flags::from_bits_truncate(cr0.bits() | WP);

    proof {
        assert(cr0.bits() & Cr0_ALL_BITS == cr0.bits()) by {
            bit_u64_and_auto();
        }
    }

    write_cr0(cr0);
}

/// Initializes the CR4 register.
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
pub fn cr4_init() {
    let mut cr4 = read_cr4();
    cr4 = Cr4Flags::from_bits_truncate(cr4.bits() | PSE | PGE | SMEP | SMAP);

    proof {
        assert(cr4.bits() & Cr4_ALL_BITS == cr4.bits()) by {
            bit_u64_and_auto();
        }
    }

    write_cr4(cr4);
}

} // verus!
