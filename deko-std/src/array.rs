use vstd::prelude::*;

use crate::prelude::*;
verus! {

/// A fixed-size array wrapper over Rust's raw array type `[T; N]`.
#[repr(C)]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct Array<T: WellFormed, const N: usize>(pub [T; N]);

// Prove it later.
pub broadcast proof fn lemma_sized_t_makes_sized_array<T: Sized + WellFormed, const N: usize>()
    ensures
        #[trigger] Array::<T, N>::size_wf(),
{
    admit();
}

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

    // /// Get the byte offset of an array element by index
    // pub open spec fn element_offset(index: nat) -> nat
    //     recommends
    //         index < N as nat,
    // {
    //     (index * core::mem::size_of::<T>()) as nat
    // }
    // /// Get the size of an array element
    // pub open spec fn element_size() -> nat {
    //     core::mem::size_of::<T>() as nat
    // }
    // /// Check if an index is within bounds
    // pub open spec fn valid_index(index: nat) -> bool {
    //     index < N as nat
    // }
    // /// Check if an offset-based access is valid
    // pub open spec fn valid_offset_access(offset: nat, access_size: nat) -> bool {
    //     &&& offset + access_size <= core::mem::size_of::<Array<T, N>>()
    //     &&& offset % (core::mem::size_of::<T>() as nat) == 0  // Aligned to element boundary
    //     &&& access_size <= core::mem::size_of::<T>()  // Don't access more than one element
    // }
    // /// Executable: Get the byte offset of an array element by index
    // ///
    // /// This is kinda weird because verus cannot know that the result
    // /// will not overflow.
    // #[verifier::external_body]
    // pub fn get_element_offset(index: usize) -> (r: usize)
    //     requires
    //         index < N,
    //         Self::size_wf(),
    //     ensures
    //         r == index * core::mem::size_of::<T>(),
    // {
    //     index * core::mem::size_of::<T>()
    // }
    // /// Write to this array using pointer and permission.
    // pub fn write_element(
    //     array_ptr: DekoPPtr<Array<T, N>>,
    //     Tracked(array_perm): Tracked<&mut DekoPointsTo<Array<T, N>>>,
    //     index: usize,
    //     value: T,
    // ) where
    //     requires
    //         array_ptr@ == old(array_perm).pptr(),
    //         old(array_perm).wf(),
    //         old(array_perm).is_init(),
    //         index < N,
    //         value.wf(),
    //     ensures
    //         array_perm.pptr() == old(array_perm).pptr(),
    //         array_perm.wf(),
    // {
    //     let offset = Self::get_element_offset(index);
    //     DekoSubPermission::write_field(array_ptr, Tracked(array_perm), offset, value)
    // }
    // /// Executable: Get a pointer to an array element
    // pub fn get_element_ptr(
    //     array_ptr: DekoPPtr<Array<T, N>>,
    //     Tracked(array_perm): Tracked<&DekoPointsTo<Array<T, N>>>,
    //     index: usize,
    // ) -> (r: *mut T)
    //     requires
    //         array_ptr@ == array_perm.pptr(),
    //         array_perm.wf(),
    //         array_perm.is_init(),
    //         index < N,
    //     ensures
    //         r as usize == array_ptr.addr() + Self::element_offset(index as nat),
    // {
    //     let offset = Self::get_element_offset(index);
    //     DekoSubPermission::get_field_ptr(array_ptr, Tracked(array_perm), offset)
    // }
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
        requires
            Self::size_wf(),
        ensures
            s.wf(),
    {
        Self(value)
    }

    pub uninterp spec fn idx(&self, i: int) -> T;

    pub uninterp spec fn idx_ptr(&self, i: int) -> DekoPPtr<T>;

    pub uninterp spec fn idx_perms(&self, i: int) -> DekoPointsTo<T>;

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
            t.1@.is_init() && t.1@.wf() && t.1@.value() == self@.index(i as int),
            t.0@ === t.1@.pptr(),
            self.idx_ptr(i as int)@ == t.0@,
            self.idx_perms(i as int) == t.1@,
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
            self.wf(),
            f.ensures((old(self)@.index(i as int),), (t, self@.index(i as int))),
            self@.len() == old(self)@.len(),
            self@.index(i as int).wf(),
            // others remain unchanged.
            forall|j: int|
                0 <= j < old(self)@.len() as int && j != i as int ==> self@.index(j) == old(
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

    closed spec fn view(&self) -> Self::V {
        Seq::new(self.spec_len() as nat, |i| self.idx(i))
    }
}

} // verus!
