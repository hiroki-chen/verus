use deko_macros::DekoDebug;
use deko_std::boxed::Box;
use deko_std::ptr::DekoPPtr;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::imp::wrmsr;
use crate::snp::rdmsr;
use crate::{kdebug, kwarn};

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

/// Represents the Local APIC of a CPU.
pub trait Apic: deko_std::fmt::DekoDebug + WellFormed {
    /// Reads the APIC ID.
    #[inline]
    fn id(&self) -> (r: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        self.apic_read(APIC_OFFSET_ID as u32)
    }

    /// Updates the APIC_BASE MSR with the given masks.
    fn apic_base(&self, and_mask: u64, or_mask: u64)
        ensures
            self.wf(),
    ;

    /// Writes `value` to the APIC register at `reg`.
    fn apic_write(&self, reg: u32, value: u32)
        requires
            self.wf(),
            reg <= 0xFF,
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
        self.apic_write(APIC_OFFSET_ICR as u32, low);
        self.apic_write((APIC_OFFSET_ICR + 1) as u32, high);
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
            wrmsr(MSR_APIC_BASE, current_value);
        } else {
            kwarn!("APIC base MSR already has the desired value: {:#x}", new_value);
        }
    }

    fn apic_write(&self, reg: u32, value: u32) {
        let msr = MSR_X2APIC_BASE + reg;

        wrmsr(msr, value as u64);
    }

    fn apic_read(&self, reg: u32) -> u32 {
        let msr = MSR_X2APIC_BASE + reg;

        rdmsr(msr) as u32
    }
}

impl WellFormed for X86Apic {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl X86Apic {
    /// Enables the x2APIC mode in the APIC.
    pub fn enable(&self) {
        let enable = 0x800 | 0x400;
        self.apic_base(!enable, enable);
    }
}

} // verus!
