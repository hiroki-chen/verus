use core::marker::PointeeSized;

use vstd::prelude::*;

verus! {

/// This function converts a `u64` number into its little-endian byte array representation.
/// However we cannot directly put `assume_specification` on [`u64::to_le_bytes`] since the
/// function signature is not understandable by Verus.
///
/// `to_le_bytes` expecte a `u8; size_of::<Self>()` but eventually relies on compiler builtin
/// to provide the implementation and the placeholder becomes some ill-formed HIRs that makes
/// Verus unhappy: `core::num::{impl0}::to_le_bytes::{constants0}`.
#[doc(hidden)]
#[inline(always)]
#[verifier::external_body]
pub fn u64_to_le_bytes(num: u64) -> (r: [u8; size_of::<u64>()])
    ensures
        r.len() == 8,
        forall|i: int| i < 8 ==> (#[trigger] r[i]) == ((num >> (i * 8)) & 0xff) as u8,
{
    num.to_le_bytes()
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(AsRefSpec via AsRefSpecImpl)]
pub trait ExAsRef<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: core::convert::AsRef<T>;

    spec fn obeys_as_ref_spec() -> bool;

    spec fn as_ref_spec(&self) -> &T;

    spec fn as_ref_requires(&self) -> bool;

    fn as_ref(&self) -> (r: &T)
        requires
            Self::obeys_as_ref_spec() ==> self.as_ref_requires(),
        ensures
            Self::obeys_as_ref_spec() ==> r == self.as_ref_spec(),
    ;
}

} // verus!
