use core::sync::atomic::AtomicU32;

use vstd::prelude::*;

use crate::hal::{PlatformApi, PlatformType};

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
}

} // verus!
