use deko_meta::{HeaderRaw, Stage2LaunchInfo};
use deko_std::prelude::*;
use vstd::prelude::*;

use crate::cpu::idt::{stage2_generic_idt_handler_no_ghcb, Idt};
use crate::cpu::register_cpuid_table;
use crate::snp::Snp;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum PlatformType {
    Snp,
    Tdx,
    None,  // not supported yet.
}

impl From<u32> for PlatformType {
    fn from(value: u32) -> Self {
        match value {
            0x0001 => PlatformType::Snp,
            0x0002 => PlatformType::Tdx,
            _ => PlatformType::None,
        }
    }
}

pub struct PlatformPredicate;

impl Predicate<PlatformType> for PlatformPredicate {
    open spec fn inv(self, platform_type: PlatformType) -> bool {
        match platform_type {
            PlatformType::Tdx | PlatformType::Snp => true,
            _ => false,
        }
    }
}

/// A global platform type that is initialized at the beginning of the program.
///
/// # Note
///
/// This is due to a bug in verus as it panics on cross-module static variable
/// references so we have to pin every static variable to the current module.
pub exec static PLATFORM: OnceLock<PlatformType, PlatformPredicate>
    ensures
        PLATFORM.wf(),
{
    OnceLock::new(Ghost(PlatformPredicate {  }))
}

/// This defines a platform abstraction to permit the Deko to run on different
/// backend CVMs. This also gives verus to reason about the high-level verifi-
/// cation logics without resorting to low-level details of the platform.
pub trait PlatformApi: Sync + Send + WellFormed {
    /// Returns the platform type of the current platform.
    fn platform_type(&self) -> PlatformType;

    /// Initializes the platform. This function should be called once at the
    /// beginning of the program to set up the platform-specific environment.
    fn init_platform(&self, header: &Stage2LaunchInfo)
        requires
            header.wf(),
            self.wf(),
    ;
}

/// Injects dummy handlers into the IDT so that we can do early-stage
/// exception handling (although this does nothing for now).
#[inline(always)]
#[verifier::external_body]
fn init_early_idt(idt: &mut Idt)
    requires
        old(idt).entries.wf(),
    ensures
        idt.wf(),
{
    unsafe {
        idt.init(&stage2_generic_idt_handler_no_ghcb as *const _ as _, 32);
    }
}

/// Sets up the environment for the platform which will setup the GDT, kernel mapping, paging,
/// kernel loading, heaps, etc.
pub fn setup_env(header: &Stage2LaunchInfo, idt: &mut Idt)
    requires
        header.wf(),
        old(idt).entries.wf(),
    ensures
        idt.wf(),
{
    // Set up the GDT.
    crate::cpu::gdt::init_gdt();

    let platform_type = PlatformType::from(header.platform_type);

    // Initialize the IDT.
    init_early_idt(idt);
    idt.load();

    // Do some platform-specific stuff.
    match platform_type {
        PlatformType::Snp => {
            let snp = Snp;
            snp.init_platform(header);
        },
        _ => {
            vstd::vpanic!("todo: ");
        },
    }

    // Now we prepare for the mapping.

    // Read the CPUID table.
    unsafe {
        register_cpuid_table(header.cpuid_page);
    }

    // Enable paging now.

}

} // verus!
