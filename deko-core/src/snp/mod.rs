use vstd::prelude::*;

use crate::hal::{PlatformApi, PlatformType};

verus! {

pub struct Snp;

impl PlatformApi for Snp {
    #[inline(always)]
    fn platform_type(&self) -> PlatformType {
        PlatformType::Snp
    }
}

} // verus!
