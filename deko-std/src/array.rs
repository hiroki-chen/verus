use vstd::prelude::*;

use crate::prelude::*;
verus! {

/// A fixed-size array wrapper over Rust's raw array type `[T; N]`.
#[repr(C)]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct Array<T: WellFormed, const N: usize>(pub [T; N]);

impl<T: WellFormed, const N: usize> Array<T, N> {
    pub open spec fn len(&self) -> usize {
        N
    }

    /// Constructs a new `Array` from a raw array.
    ///
    /// This is marked as external_body because the inner type is opaque.
    #[verifier::external_body]
    pub const fn new(value: [T; N]) -> (s: Self)
        ensures
            s@ =~= Seq::new(N as nat, |i| s.idx(i)),
    {
        Self(value)
    }

    pub uninterp spec fn idx(&self, i: int) -> T;

    #[verifier::inline]
    pub open spec fn to_seq(&self) -> Seq<T> {
        self@
    }
}

impl<T: WellFormed + Copy, const N: usize> Array<T, N> {
    #[verifier::external_body]
    pub const fn fill(elem: T) -> (s: Self)
        ensures
            s@ =~= Seq::new(N as nat, |i| elem),
    {
        Self([elem;N])
    }
}

impl<T: WellFormed, const N: usize> View for Array<T, N> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Self::V {
        Seq::new(self.len() as nat, |i| self.idx(i))
    }
}

} // verus!
