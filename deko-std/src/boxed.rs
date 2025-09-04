//! Heap-allocated objects like boxes.
// use alloc::boxed::Box as BoxInner;
use vstd::prelude::*;

use crate::prelude::*;

verus! {

// A pointer type that uniquely owns a heap allocation of type `T`.
///
/// Note that this is our wrapper around the Box coming from standard library.
/// 
/// This struct is allocated from the `heap` which we assume is already configured
/// and mapped properly. Thus, the address obtained by referencing it is the
/// virtual address that can be used to access the memory.
/// 
/// In some cases where we want to allocate a [`Box`] directly from the physical
/// memory and bypass the MMU. please use [`RawBox`] instea.
#[verifier::reject_recursive_types(V)]
pub struct Box<V, F> {
    ptr: DekoPPtr<V>,
    inv: Ghost<F>,
}

/// A thin wrapper around `DekoPointsTo<V>` that is used to track the points-to relation
/// of a `Box<V, F>`.
pub tracked struct BoxPointsTo<V> {
    points_to: DekoPointsTo<V>,
}

impl<T: WellFormed, F> View for Box<T, F> {
    type V = DekoPPtr<T>;

    closed spec fn view(&self) -> Self::V {
        self.ptr
    }
}

impl<T: WellFormed> View for BoxPointsTo<T> {
    type V = DekoPointsTo<T>;

    closed spec fn view(&self) -> Self::V {
        self.points_to
    }
}

impl<V: WellFormed, F: Predicate<V>> Box<V, F> {
    pub closed spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn inv(&self, v: V) -> bool {
        self.inv@.inv(v)
    }

    #[inline]
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a BoxPointsTo<V>>) -> (r: &'a V)
        requires
            self.wf(),
            perm@.pptr() === self@@,
            perm@.is_init(),
            perm@.mem_wf(),
        ensures
            *r == perm@.value(),
    {
        self.ptr.borrow(Tracked(&perm.points_to))
    }

    /// Allocates memory on the heap and then places `x` into it.
    ///
    /// The users need to provide the allocator with an invariant function `f` that
    /// is used to verify the memory contents.
    pub fn new(x: V, allocator: &DefaultDekoHeapAllocator, Ghost(f): Ghost<F>) -> (s: (
        Self,
        Tracked<BoxPointsTo<V>>,
    ))
        requires
            allocator.wf(),
            f.inv(x),
        ensures
            s.0.wf(),
            s.0.inv(x),
            s.1@@.pptr() === s.0@@,
            s.1@@.is_init(),
            s.1@@.value() == x,
            s.1@@.mem_wf(),
    {
        let (pptr, Tracked(pptr_perm)) = DekoPPtr::new(x, allocator);

        let tracked boxed_pt = BoxPointsTo { points_to: pptr_perm };

        (Self { ptr: pptr, inv: Ghost(f) }, Tracked(boxed_pt))
    }
}

} // verus!
