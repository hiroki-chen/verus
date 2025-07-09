use core::sync::atomic::AtomicU32;

use deko_macros::bits;
use deko_proofs::prelude::*;
use vstd::prelude::*;

use crate::hal::{PlatformApi, PlatformType};

pub mod snpcall;

extern "C" {
    /// A global flag to indicate whether the AP has been started.
    static mut ap_flag: AtomicU32;
}

verus! {

// #[bits(RmpAttribute, u64)]
#[repr(C, align(1))]
pub struct __RmpAttribute {
    // #[bit(0, 7)]
    pub vmpl: u64,
    // #[bit(8, 15)]
    pub perm: u64,
    // #[bit(16, 16)]
    pub vmsa: u64,
}

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
