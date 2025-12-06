use tla::*;
use vstd::prelude::*;

use crate::sync::mutex::{Spin, SpinNoIrq};
use crate::WellFormed;

verus! {

/// An experimental mutex implementation for TLA+ based reasoning.
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(S)]
pub struct Mutex<V: WellFormed, S: Spin> {
    marker: core::marker::PhantomData<(V, S)>,
}

} // verus!
