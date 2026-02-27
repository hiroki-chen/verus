use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

pub const DEKO_CS: u16 = 1 * 8;

pub const DEKO_DS: u16 = 2 * 8;

pub const DEKO_USER_CS: u16 = 3 * 8;

pub const DEKO_USER_DS: u16 = 4 * 8;

pub const DEKO_TSS: u16 = 6 * 8;

pub const DEKO_CS_ATTRIBUTES: u16 = 0xa09b;

pub const DEKO_DS_ATTRIBUTES: u16 = 0xc093;

pub const DEKO_TR_ATTRIBUTES: u16 = 0x89;

pub const MSR_LSTAR: u32 = 0xC0000082;

pub const MSR_FS_BASE: u32 = 0xC000_0100;

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
        const OSXSAVE = 18; // XSAVE and Processor Extended States Enable
        const SMEP = 20; // Supervisor Mode Execution Protection
        const SMAP = 21; // Supervisor Mode Access Prevention
    }
}

deko_bitflags! {
    pub struct Efer: u64 {
        const SCE = 0; // System Call Extensions
        const LME = 8; // Long Mode Enable
        const LMA = 10; // Long Mode Active
        const NXE = 11; // No-Execute Enable
        const SVME = 12; // Secure Virtual Machine Enable
        const LMSLE = 13; // Long Mode Segment Limit Enable
        const FFXSR = 14; // Fast FXSAVE/FXRSTOR
        const TCE = 15; // Translation Cache Extension
        const MCOMMIT = 17; // MCOMMIT Enable
        const INTWB = 18; // INTWB Enable
        const UAIE = 20; // User Access Instruction Enable
    }
}

#[inline]
#[verifier::external_body]
pub fn write_fs_base(fs_base: u64) {
    unsafe {
        core::arch::asm!(
            "wrmsr",
            in("ecx") MSR_FS_BASE,
            in("eax") (fs_base & 0xFFFF_FFFF) as u32,
            in("edx") (fs_base >> 32) as u32,
            options(att_syntax),
        );
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

#[inline]
#[verifier::external_body]
pub fn read_cr2() -> u64 {
    let mut cr2: u64;

    unsafe {
        core::arch::asm!(
            "movq %cr2, {}",
            out(reg) cr2,
            options(att_syntax)
        );
    }

    cr2
}

#[inline]
#[verifier::external_body]
pub fn read_cr3() -> u64 {
    let mut cr3: u64;

    unsafe {
        core::arch::asm!(
            "movq %cr3, {}",
            out(reg) cr3,
            options(att_syntax)
        );
    }

    cr3
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

/// Reads the current value of the EFER MSR.
#[inline]
#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    ensures
        r.wf(),
        r.bits() & Efer_ALL_BITS == r.bits(),
)]
pub fn read_efer() -> EferFlags {
    let low: u32;
    let high: u32;

    unsafe {
        core::arch::asm!(
            "rdmsr",
            in("ecx") 0xc0000080u32,
            out("eax") low,
            out("edx") high,
            options(att_syntax),
        );
    }

    EferFlags::from_bits_truncate(((high as u64) << 32) | (low as u64))
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
        "mov {}, %cr3",
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

#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
pub fn osfxsr_init() {
    let mut cr4 = read_cr4();
    cr4 = Cr4Flags::from_bits_truncate(cr4.bits() | OSFXSR);

    proof {
        assert(cr4.bits() & Cr4_ALL_BITS == cr4.bits()) by {
            bit_u64_and_auto();
        }
    }

    write_cr4(cr4);
}

pub fn sse_cr0_init() {
    let mut cr0 = read_cr0();
    cr0 = Cr0Flags::from_bits_truncate(cr0.bits() & !(EM | TS) | MP);
    proof {
        assert(cr0.bits() & Cr0_ALL_BITS == cr0.bits()) by {
            bit_u64_and_auto();
        }
    }

    write_cr0(cr0);
}

pub fn xsave_init() {
    let mut cr4 = read_cr4();
    cr4 = Cr4Flags::from_bits_truncate(cr4.bits() | OSXSAVE);
    proof {
        assert(cr4.bits() & Cr4_ALL_BITS == cr4.bits()) by {
            bit_u64_and_auto();
        }
    }

    write_cr4(cr4);
}

#[verifier::external_body]
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
pub fn xcr0_init() {
    unsafe {
        core::arch::x86_64::_xsetbv(0, 0b111);  // Enable x87, SSE, AVX
    }
}

#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
pub fn sse_init() {
    osfxsr_init();
    sse_cr0_init();
    xsave_init();
    xcr0_init();
}

#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
#[verifier::external_body]
#[inline]
pub fn sse_restore_context(addr: u64) {
    unsafe {
        core::arch::x86_64::_xrstor(addr as *const u8, 0b111);
    }
}

#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
#[verifier::external_body]
#[inline]
pub fn sse_save_context(addr: u64) {
    unsafe {
        core::arch::x86_64::_xsave(addr as *mut u8, 0b111);
    }
}

#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
#[verifier::external_body]
#[inline]
pub fn disable_smap() {
    unsafe {
        core::arch::asm!(
            "clac",
            options(att_syntax, nomem, nostack),
        );
    }
}

#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    // requires
    // ensures
)]
#[verifier::external_body]
#[inline]
pub fn enable_smap() {
    unsafe {
        core::arch::asm!(
            "stac",
            options(att_syntax, nomem, nostack),
        );
    }
}

/// Executes the given closure `f` with SMAP disabled.
#[verus_spec(r =>
    // with Tracked(cpu_core): Tracked<&mut DekoCpuCore>,
    requires
        f.requires(()),
    // ensures
)]
pub fn no_smap_zone<T, F: FnOnce() -> T>(f: F) -> T {
    disable_smap();
    let t = f();
    enable_smap();

    t
}

} // verus!
