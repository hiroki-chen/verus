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

    pub uninterp spec fn id(&self) -> usize;

    pub fn len(&self) -> (res: usize)
        ensures
            self.spec_len() == res,
    {
        N
    }

    /// Constructs a new [`Array`] from a raw array.
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

    /// Takes a value out of the collection at index `i`, leaving a temporary hole.
    ///
    /// This function is the first half of a "take-and-replace" or "hole" pattern. It efficiently
    /// removes an element from the collection by moving it out and replacing its slot with
    /// uninitialized memory. This avoids the cost of shifting subsequent elements, as `Vec::remove`
    /// would do.
    ///
    /// It returns a tuple containing two items:
    /// 1. The owned value `T` that was previously at index `i`.
    /// 2. A ghost `Tracked<DekoHoleToken>`. This token is a compile-time proof that a "hole"
    ///    now exists in the collection. It represents the caller's obligation to fill this
    ///    hole later, typically by calling a corresponding `restore` method. The token itself
    ///    has no runtime representation.
    ///
    /// Because this function leaves the collection in a temporarily invalid state (containing
    /// uninitialized memory), it is marked as `unsafe`. The caller must uphold the safety
    /// contract to prevent Undefined Behavior.
    ///
    /// # Verus-Specific Notes
    ///
    /// This function is marked `#[verifier::external_body]`, meaning its implementation is trusted
    /// by Verus. A fully specified public API would wrap this function and provide `requires` and
    /// `ensures` clauses to formally prove the safety of the entire operation. The `ensures`
    /// clause would state that the returned token corresponds to a hole at index `i`.
    ///
    /// For example, a safe wrapper would look like:
    /// ```rust,ignore
    /// pub fn update_at(&mut self, i: usize, f: impl FnOnce(T) -> T)
    ///     requires
    ///         /* ... preconditions ... */,
    ///     ensures
    ///         /* ... postconditions ... */,
    /// {
    ///     let (value, Tracked(token)) = unsafe { self.take(i) };
    ///     let new_value = f(value);
    ///     unsafe { self.restore(i, new_value, Tracked(token)) };
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The caller must guarantee the following conditions to prevent Undefined Behavior:
    ///
    /// 1.  The index `i` must be a valid, in-bounds index for the underlying collection (`self.0`).
    ///     Calling with an out-of-bounds index will likely cause a panic.
    ///
    /// 2.  **The most critical contract:** After this function is called, the collection `self`
    ///     is in an invalid state. The caller **MUST** eventually use the returned `DekoHoleToken`
    ///     to restore a valid, initialized value of type `T` into the slot at index `i`.
    ///
    /// 3.  Failure to restore the hole before the collection is dropped, or before any other
    ///     operation accesses the element at index `i`, will lead to **Undefined Behavior**,
    ///     as it would involve reading or dropping uninitialized memory.
    #[verifier::external_body]
    unsafe fn take(&mut self, i: usize) -> (t: (T, Tracked<DekoHoleToken<'_, T>>))
        requires
            0 <= i < old(self).spec_len() as usize,
            old(self).wf(),
        ensures
            self.wf(),
            self@.len() == old(self)@.len() - 1,  // "as-if"
            t.0 == self@.index(i as int),
            t.1@.id() == (self.id(), i),
            old(self).id() == self.id(),
    {
        let bad_mem = core::mem::MaybeUninit::uninit().assume_init();
        let res = core::mem::replace(&mut self.0[i], bad_mem);

        (res, Tracked(DekoHoleToken::new(self.id(), i)))
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
