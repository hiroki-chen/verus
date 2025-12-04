use core::marker::PointeeSized;

use vstd::prelude::*;

verus! {

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
