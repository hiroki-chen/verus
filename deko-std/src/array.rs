use vstd::prelude::*;

use crate::prelude::*;
verus! {

/// A fixed-size array wrapper over Rust's raw array type `[T; N]`.
#[repr(C)]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct Array<T: WellFormed, const N: usize>(pub [T; N]);

impl<T: WellFormed, const N: usize> WellFormed for Array<T, N> {
    open spec fn wf(&self) -> bool {
        &&& self@ =~= Seq::new(N as nat, |i| self.idx(i))
        &&& forall|i: int| 0 <= i < N as int ==> #[trigger] self@.index(i).wf()
    }
}

impl<T: WellFormed, const N: usize> Array<T, N> {
    pub open spec fn spec_len(&self) -> usize {
        N
    }

    pub fn len(&self) -> (res: usize)
        ensures
            self.spec_len() == res,
    {
        N
    }

    /// Constructs a new `Array` from a raw array.
    ///
    /// This is marked as external_body because the inner type is opaque.
    #[verifier::external_body]
    pub const fn new(value: [T; N]) -> (s: Self)
        ensures
            s.wf(),
    {
        Self(value)
    }

    pub uninterp spec fn idx(&self, i: int) -> T;

    #[verifier::inline]
    pub open spec fn to_seq(&self) -> Seq<T> {
        self@
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn index(&self, i: usize) -> (t: &T)
        requires
            0 <= i < self.spec_len() as usize,
            self.wf(),
        ensures
            *t == self@.index(i as int),
    {
        &self.0[i]
    }

    #[verifier::external_body]
    pub fn update_in_place(&mut self, i: usize, f: impl Fn(&mut T) -> ())
        requires
            0 <= i < old(self).spec_len() as usize,
            old(self).wf(),
            call_requires(f, (v,)),
        ensures
            self.wf(),
            // find a way to express this
            // self@.index(i as int) == f(old(self)@.index(i as int)),
    {
        use core::ops::IndexMut;
        // not supported by verus yet ??
        f(self.0.index_mut(i));
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn update(&mut self, i: usize, value: T) -> (t: T)
        requires
            0 <= i < old(self)@.len() as usize,
            old(self).wf(),
            value.wf(),
        ensures
            old(self)@.index(i as int) == t,
            self@.index(i as int) == value,
            self.wf(),
            self@ == old(self)@.update(i as int, value),
    {
        // not supported by verus yet
        core::mem::replace(&mut self.0[i], value)
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
        Seq::new(self.spec_len() as nat, |i| self.idx(i))
    }
}

} // verus!
