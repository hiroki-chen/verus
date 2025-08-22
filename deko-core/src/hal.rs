use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

#[repr(u64)]
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum PlatformType {
    Tdx = 0x0001,
    Snp = 0x0002,
    None,  // not supported yet.
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

impl From<u64> for PlatformType {
    fn from(value: u64) -> Self {
        match value {
            0x0001 => PlatformType::Tdx,
            0x0002 => PlatformType::Snp,
            _ => PlatformType::None,
        }
    }
}

/// This defines a platform abstraction to permit the Deko to run on different
/// backend CVMs. This also gives verus to reason about the high-level verifi-
/// cation logics without resorting to low-level details of the platform.
pub trait PlatformApi: Sync + Send {
    /// Returns the platform type of the current platform.
    fn platform_type(&self) -> PlatformType;

    /// Initializes the platform. This function should be called once at the
    /// beginning of the program to set up the platform-specific environment.
    fn init_platform(&self);
}

fn init_early_idt() {
}

/// Sets up the environment for the platform which will setup the GDT, kernel mapping, paging,
/// kernel loading, heaps, etc.
fn setup_env() {
    crate::cpu::gdt::init_gdt();
}

#[verifier::external_body]
pub fn init_platform(platform_type: PlatformType) {
    // This is buggy as verus has problem dealing with statics.
    // We will remove `external_body` once the bug is fixed.
    PLATFORM.init(platform_type);

    setup_env();

    match platform_type {
        PlatformType::Tdx => {
            // Initialize TDX platform.
        },
        PlatformType::Snp => {
            // Initialize SNP platform.
        },
        _ => {},
    }
}

} // verus!
