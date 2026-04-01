use core::ops::Add;

use vstd::prelude::*;

use crate::prelude::*;

verus! {

/// A fixed-size array wrapper over Rust's raw array type `[T; N]`.
#[repr(C)]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[deprecated(
    note = "Use [T; N] directly with Verus' built-in support for arrays. This type will be removed in a future release."
)]
pub struct Array<T: WellFormed, const N: usize>(pub [T; N]);

// Prove it later.
pub broadcast axiom fn lemma_sized_t_makes_sized_array<T: Sized + WellFormed, const N: usize>()
    ensures
        #[trigger] Array::<T, N>::size_wf(),
;

impl<T: WellFormed, const N: usize> WellFormed for Array<T, N> {
    open spec fn wf(&self) -> bool {
        &&& Self::size_wf()
        &&& self@ =~= Seq::new(N as nat, |i| self.idx(i))
        &&& forall|i: int| 0 <= i < N as int ==> #[trigger] self@.index(i).wf()
    }
}

impl<T: WellFormed, const N: usize> Array<T, N> {
    /// Ensures we are constructing meaningful arrays
    pub open spec fn size_wf() -> bool {
        &&& vstd::layout::size_of::<T>() as usize as int == vstd::layout::size_of::<
            T,
        >()  // size_of fits in usize
        &&& vstd::layout::size_of::<Self>() as usize as int == vstd::layout::size_of::<
            Self,
        >()  // size_of fits in usize
        &&& core::mem::size_of::<T>()
            > 0  // for simplicity, we do not support zero-sized types
        &&& N * core::mem::size_of::<T>() == core::mem::size_of::<Self>()
        &&& core::mem::size_of::<Self>() <= usize::MAX
        &&& forall|i: usize|
            i < N ==> #[trigger] (i * core::mem::size_of::<T>()) <= core::mem::size_of::<Self>()
                - core::mem::size_of::<T>()
    }

    pub open spec fn spec_len(&self) -> usize {
        N
    }

    pub uninterp spec fn id(&self) -> usize;

    pub fn len(&self) -> (res: usize)
        ensures
            self.spec_len() == res,
            res == self@.len(),
    {
        N
    }

    /// Constructs a new [`Array`] from a raw array.
    ///
    /// This is marked as external_body because the inner type is opaque.
    #[verifier::external_body]
    pub const fn new(value: [T; N]) -> (s: Self)
        requires
            Self::size_wf(),
        ensures
            s.wf(),
            forall|i: int| 0 <= i < N as int ==> s@.index(i) == #[trigger] value@[i as int],
    {
        Self(value)
    }

    pub uninterp spec fn idx(&self, i: int) -> T;

    pub uninterp spec fn idx_ptr(&self, i: int) -> DekoPPtr<T>;

    #[verifier::inline]
    pub open spec fn to_seq(&self) -> Seq<T> {
        self@
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn index(&self, i: usize) -> (t: &T)
        requires
            i < self@.len() as usize,
            self.wf(),
        ensures
            *t == self@.index(i as int),
            t.wf(),
        opens_invariants none
        no_unwind
    {
        &self.0[i]
    }

    /// In case we need to index the element as pointers. As Verus does not support
    /// direct case from `&T` to `DekoPPtr<T>`, we need to go through raw pointer first.
    /// We also does return the permission as borrowed to ensure no one else can modify
    /// the data while we have the pointer.
    #[verifier::external_body]
    #[inline(always)]
    pub fn index_as_ptr(&self, i: usize) -> (t: (DekoPPtr<T>, Tracked<&DekoPointsTo<T>>))
        requires
            0 <= i < self.spec_len() as usize,
            self.wf(),
        ensures
            t.1@.is_init(),
            t.1@.wf(),
            t.1@.value() == self@.index(i as int),
            t.0@ === t.1@.pptr(),
            self.idx_ptr(i as int)@ == t.0@,
    {
        let (ptr, Tracked(perm)) = unsafe { DekoPPtr::from_raw_uninit(&self.0[i] as *const T as u64)
        };

        (ptr, Tracked(&perm))
    }

    #[verifier::external_body]
    pub fn update_in_place<U>(&mut self, i: usize, f: impl FnOnce(T) -> (U, T)) -> (t: U)
        requires
            0 <= i < old(self)@.len(),
            old(self).wf(),
            old(self)@.index(i as int).wf(),
            f.requires((old(self)@.index(i as int),)),
        ensures
            final(self).wf(),
            f.ensures((old(self)@.index(i as int),), (t, final(self)@.index(i as int))),
            final(self)@.len() == old(self)@.len(),
            final(self)@.index(i as int).wf(),
            // others remain unchanged.
            forall|j: int|
                0 <= j < old(self)@.len() as int && j != i as int ==> final(self)@.index(j) == old(
                    self,
                )@.index(j),
    {
        let bad = unsafe { core::mem::MaybeUninit::<T>::uninit().assume_init() };
        let v = core::mem::replace(&mut self.0[i], bad);
        let (t, v) = f(v);
        self.0[i] = v;

        t
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn update(&mut self, i: usize, value: T) -> (t: T)
        requires
            0 <= (i as int) < old(self)@.len(),
            old(self).wf(),
            value.wf(),
        ensures
            old(self)@.index(i as int) == t,
            final(self)@.index(i as int) == value,
            final(self).wf(),
            final(self)@ == old(self)@.update(i as int, value),
    {
        // not supported by verus yet
        core::mem::replace(&mut self.0[i], value)
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn as_ptr(&self) -> (p: DekoPPtr<T>)
        requires
            self.wf(),
    {
        let ptr = self.0.as_ptr() as usize;
        DekoPPtr(vstd::simple_pptr::PPtr(ptr, core::marker::PhantomData))
    }
}

impl<T: WellFormed + Copy, const N: usize> Array<T, N> {
    #[verifier::external_body]
    pub const fn fill(elem: T) -> (s: Self)
        requires
            Self::size_wf(),
        ensures
            s@ =~= Seq::new(N as nat, |i| elem),
            s.wf(),
    {
        Self([elem;N])
    }
}

impl<T: WellFormed, const N: usize> View for Array<T, N> {
    type V = Seq<T>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.spec_len() as nat, |i| self.idx(i))
    }
}

#[verifier::external]
impl<T: WellFormed, const N: usize> core::fmt::Debug for Array<T, N> where T: core::fmt::Debug {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl<T: WellFormed + Clone, const N: usize> Clone for Array<T, N> {
    #[verifier::external_body]
    fn clone(&self) -> (r: Self)
        ensures
            r.wf(),
            r@ == self@,
    {
        Array(self.0.clone())
    }
}

impl<T: WellFormed + Copy, const N: usize> Copy for Array<T, N> {

}

impl<const N: usize> Array<u8, N> {
    #[verifier::external_body]
    pub fn as_str(&self) -> (s: &str)
        requires
            self.wf(),
            forall|i: int| 0 <= i < N ==> 0 <= #[trigger] self@[i] < 128,
        ensures
            s@.len() == N,
            forall|i: int| i < N ==> s@[i] == #[trigger] self@[i as int],
    {
        let slice = &self.0;
        unsafe { core::str::from_utf8_unchecked(slice) }
    }
}

impl<T: WellFormed + PartialEq<U>, U: WellFormed, const N: usize> core::cmp::PartialEq<
    Array<U, N>,
> for Array<T, N> {
    #[verifier::external_body]
    fn eq(&self, other: &Array<U, N>) -> bool {
        self.0 == other.0
    }
}

impl<T: WellFormed + PartialEq<U>, U: WellFormed, const N: usize> core::cmp::PartialEq<
    [U],
> for Array<T, N> {
    #[verifier::external_body]
    fn eq(&self, other: &[U]) -> bool {
        self.0 == *other
    }
}

} // verus!
