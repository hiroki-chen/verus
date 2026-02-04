//! A bounce buffer for system calls that cross VMPL boundaries.
use deko_macros::DekoDebug;
use vstd::prelude::*;

verus! {

/// A bounce buffer used for copying data between different VMPLs.
#[derive(DekoDebug)]
pub struct DekoBounceBuffer {}

#[verus_verify]
impl DekoBounceBuffer {

}

} // verus!
