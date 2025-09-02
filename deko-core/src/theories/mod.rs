use deko_meta::*;
use deko_std::prelude::*;
use vstd::prelude::*;

verus! {

#[verifier::nonlinear]
pub proof fn stage2_heap_valid_params()
    ensures
        valid_heap_param(
            STAGE2_HEAP_START as u64,
            (STAGE2_HEAP_END - STAGE2_HEAP_START) as u64,
            HEAP_SIZE as u64,
        ),
{
    admit();
}

} // verus!
