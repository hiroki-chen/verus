use vstd::prelude::*;

verus! {

/// A fixed-size array wrapper over Rust's raw array `[T; N]`.
#[derive(Copy)]
#[repr(C)]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct Array<T: Clone, const N: usize> {
    pub inner: [T; N],
}

impl<T: Clone, const N: usize> Clone for Array<T, N> {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        Array { inner: self.inner.clone() }
    }
}

} // verus!
