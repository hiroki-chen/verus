use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub tracked struct CpuCoreIdPerm {
    _prop: NoCopy,
}

} // verus!
