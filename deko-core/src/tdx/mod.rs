pub mod error;
pub mod tdcall;

use vstd::prelude::*;

use crate::hal::{PlatformApi, PlatformType};

verus! {

pub struct Tdx;

impl PlatformApi for Tdx {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Tdx
    }
}

} // verus!
