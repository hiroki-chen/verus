use deko_std::sync::POnceCell;
use vstd::prelude::*;

verus! {

pub exec static PLATFORM: POnceCell<PlatformType> = POnceCell::new();

pub enum PlatformType {
    Tdx,
    Snp,
    None,  // not supported yet.
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

} // verus!
