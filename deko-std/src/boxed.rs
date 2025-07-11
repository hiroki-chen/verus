//! Heap-allocated objects like boxes.
use alloc::alloc::{Allocator, Global};
use alloc::boxed::Box as BoxInner;
use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

verus! {

/// A pointer type that uniquely owns a heap allocation of type `T`.
/// 
/// Note that this is our wrapper around the Box coming from standard library.
#[verifier::reject_recursive_types(V)]
#[verifier::external_body]
pub struct Box<V> {
    box_inner: BoxInner<V>,
}

impl<V> Box<V> {
    pub uninterp spec fn wf(&self) -> bool;

    pub uninterp spec fn id(&self) -> int;

    pub uninterp spec fn view(&self) -> V;
}

} // verus!
