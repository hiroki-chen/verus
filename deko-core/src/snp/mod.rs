use core::sync::atomic::AtomicU32;

use vstd::prelude::*;

use crate::hal::{PlatformApi, PlatformType};

pub mod snpcall;

#[cfg(feature = "logging")]
pub(crate) mod logging;

extern "C" {
    /// A global flag to indicate whether the AP has been started.
    static mut ap_flag: AtomicU32;
}

verus! {

pub struct Snp;

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }

    fn init_platform(&self) {
        // Initialize the SNP platform.
    }
}

impl Snp {

}

} // verus!
