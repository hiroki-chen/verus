//! Heap-allocated objects like boxes.
// use alloc::boxed::Box as BoxInner;
use vstd::prelude::*;

use crate::ptr::DekoPPtr;

verus! {

/// A pointer type that uniquely owns a heap allocation of type `T`.
///
/// Note that this is our wrapper around the Box coming from standard library.
#[verifier::reject_recursive_types(V)]
pub struct Box<V>(DekoPPtr<V>);

impl<V> Box<V> {
    pub closed spec fn wf(&self) -> bool {
        self.0.addr() != 0
    }

    pub uninterp spec fn id(&self) -> int;

    pub uninterp spec fn view(&self) -> V;
}

} // verus!
