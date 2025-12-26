use deko_macros::DekoDebug;
use deko_std::bits::bit_u64_and_auto;
use deko_std::boxed::Box;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::cpu::CPUID_MAX_COUNT;
use crate::imp::ghcb::GuestHostCommunicationBlock;
use crate::imp::{wrmsr, SnpStatusFlags, REST_INJ};
use crate::snp::rdmsr;
use crate::{kdebug, kpanic_if, kwarn};

verus! {

#[derive(DekoDebug)]
pub struct X86Apic;

pub const MSR_X2APIC_BASE: u32 = 0x800;

/// APIC Base MSR
pub const MSR_APIC_BASE: u32 = 0x1B;

/// Local APIC ID register MSR offset
pub const APIC_OFFSET_ID: usize = 0x2;

/// End-of-Interrupt register MSR offset
pub const APIC_OFFSET_EOI: usize = 0xB;

/// Spurious-Interrupt-Register MSR offset
pub const APIC_OFFSET_SPIV: usize = 0xF;

/// Interrupt-Service-Register base MSR offset
pub const APIC_OFFSET_ISR: usize = 0x10;

/// Interrupt-Control-Register register MSR offset
pub const APIC_OFFSET_ICR: usize = 0x30;

/// SELF-IPI register MSR offset (x2APIC only)
pub const APIC_OFFSET_SELF_IPI: usize = 0x3F;

/// Software Enable bit mask for Spurious Interrupt Vector Register
pub const APIC_SPIV_SW_ENABLE_MASK: u64 = 1 << 8;

/// Represents the Local APIC of a CPU.
pub trait Apic: deko_std::fmt::DekoDebug + WellFormed {
    /// Reads the APIC ID.
    #[inline]
    fn id(&self) -> (r: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
            r < CPUID_MAX_COUNT,
    {
        let r = self.apic_read(APIC_OFFSET_ID as u32);
        kpanic_if!(r >= CPUID_MAX_COUNT as u32, "APIC ID {} exceeds maximum CPU count {}", r, CPUID_MAX_COUNT);
        r
    }

    /// Updates the APIC_BASE MSR with the given masks.
    fn apic_base(&self, and_mask: u64, or_mask: u64)
        ensures
            self.wf(),
    ;

    /// Writes `value` to the APIC register at `reg`.
    fn apic_write(&self, reg: u32, value: u64)
        requires
            self.wf(),
            reg <= 0xFF,
    ;

    fn spiv_write(&self, vector: u8, enable: bool)
        requires
            self.wf(),
    ;

    /// Reads the APIC register at `reg`.
    fn apic_read(&self, reg: u32) -> u32
        requires
            self.wf(),
            reg <= 0xFF,
    ;

    fn icr_write(&self, low: u32, high: u32)
        requires
            self.wf(),
    {
        broadcast use SnpStatusFlags::lemma_each_bit_is_valid;

        if SnpStatusFlags::get_status().contains(REST_INJ) {
            kdebug!("RESTRICTED INJ");
            // Forward this to HV doorbell.
            let (ghcb, Tracked(perm)) = crate::snp::ghcb::current_ghcb();
            GuestHostCommunicationBlock::hv_ipi(
                ghcb,
                Tracked(perm),
                (low as u64 | ((high as u64) << 32)),
            );
        } else {
            self.apic_write(APIC_OFFSET_ICR as u32, (low as u64 | ((high as u64) << 32)));
        }
    }

    /// End of Interrupt signal to the APIC.
    fn eoi(&self)
        requires
            self.wf(),
    {
        self.apic_write(APIC_OFFSET_EOI as u32, 0);
    }
}

impl Apic for X86Apic {
    fn apic_base(&self, and_mask: u64, or_mask: u64)
        ensures
            self.wf(),
    {
        let current_value = rdmsr(MSR_APIC_BASE);

        kdebug!("Current APIC base MSR value:", current_value => hex);
        let new_value = (current_value & and_mask) | or_mask;
        kdebug!("Updating APIC base MSR to:", new_value => hex);

        if current_value != new_value {
            wrmsr(MSR_APIC_BASE, new_value);
        } else {
            kwarn!("APIC base MSR already has the desired value: {:#x}", new_value);
        }
    }

    fn apic_write(&self, reg: u32, value: u64) {
        let msr = MSR_X2APIC_BASE + reg;

        wrmsr(msr, value);
    }

    fn apic_read(&self, reg: u32) -> u32 {
        let msr = MSR_X2APIC_BASE + reg;

        rdmsr(msr) as u32
    }

    fn spiv_write(&self, vector: u8, enable: bool) {
        let apic_spiv = if enable {
            APIC_SPIV_SW_ENABLE_MASK
        } else {
            0
        } | ((vector as u64) & 0xFF);

        self.apic_write(APIC_OFFSET_SPIV as u32, apic_spiv);
    }
}

impl WellFormed for X86Apic {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl X86Apic {
    /// Enables the x2APIC mode in the APIC.
    #[inline]
    pub fn enable(&self) {
        let enable = 0x800 | 0x400;
        self.apic_base(!enable, enable);
    }

    #[inline]
    pub fn sw_enable(&self) {
        self.spiv_write(0xFF, true);
    }
}

} // verus!
