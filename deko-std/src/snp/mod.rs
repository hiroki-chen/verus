pub mod ghcb;

use vstd::prelude::*;

verus! {

/// The MSR used to support the GHCB MSR Protocol. For more
/// details, please refer to SEV-ES GHCB standardization doc
/// published by AMD.
pub const MSR_AMD64_SEV_ES_GHCB: u32 = 0xC001_0130;

} // verus!
