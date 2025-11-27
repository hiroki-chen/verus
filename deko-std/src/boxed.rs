//! Heap-allocated objects like boxes.
// use alloc::boxed::BoxInner as BoxInner;
use vstd::prelude::*;

use crate::prelude::*;

verus! {

/// Re-export
pub type Box<T> = BoxInner<T, ()>;

pub type BoxWithPred<T, F> = BoxInner<T, F>;

impl<T: WellFormed> Box<T> {
    #[inline]
    pub fn new(x: T, allocator: &DefaultDekoHeapAllocator) -> (s: (Self, Tracked<BoxPointsTo<T>>))
        requires
            allocator.wf(),
        ensures
            s.0.wf(),
            s.0.inv(x),
            s.1@@.pptr() === s.0@@,
            s.1@@.is_init(),
            s.1@@.value() == x,
            s.1@@.mem_wf(),
            s.1@@.wf(),
    {
        Self::new_with_f(x, allocator, Ghost(()))
    }

    #[inline]
    pub fn new_zeroed(allocator: &DefaultDekoHeapAllocator) -> (s: (Self, Tracked<BoxPointsTo<T>>))
        requires
            allocator.wf(),
        ensures
            s.0.wf(),
            s.1@@.wf(),
            s.1@@.pptr() === s.0@@,
            s.1@@.is_uninit(),
    {
        Self::new_zeroed_with_f(allocator, Ghost(()))
    }
}

// A pointer type that uniquely owns a heap allocation of type `T`.
///
/// Note that this is our wrapper around the BoxInner coming from standard library.
///
/// This struct is allocated from the `heap` which we assume is already configured
/// and mapped properly. Thus, the address obtained by referencing it is the
/// virtual address that can be used to access the memory.
///
/// In some cases where we want to allocate a [`BoxInner`] directly from the physical
/// memory and bypass the MMU. please use [`RawBox`] instea.
#[verifier::reject_recursive_types(V)]
pub struct BoxInner<V: WellFormed, F> {
    ptr: DekoPPtr<V>,
    inv: Ghost<F>,
}

/// A thin wrapper around `DekoPointsTo<V>` that is used to track the points-to relation
/// of a `BoxInner<V, F>`.
pub tracked struct BoxPointsTo<V: WellFormed> {
    points_to: DekoPointsTo<V>,
}

impl<T: WellFormed, F> View for BoxInner<T, F> {
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

impl<V: WellFormed, F: Predicate<V>> BoxInner<V, F> {
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
            perm@.wf(),
        ensures
            *r == perm@.value(),
    {
        self.ptr.borrow(Tracked(&perm.points_to))
    }

    #[inline]
    pub fn write(&self, Tracked(perm): Tracked<&mut BoxPointsTo<V>>, v: V)
        requires
            v.wf(),
            self.wf(),
            self.inv(v),
            old(perm)@.pptr() == self@@,
            old(perm)@.wf(),
        ensures
            perm@.pptr() === self@@,
            perm@.is_init(),
    {
        self.ptr.write(Tracked(&mut perm.points_to), v)
    }

    /// Allocates memory on the heap and leaves it uninitialized.
    ///
    /// Please note that [`Box`] is just initialized on the heap allocated by the
    /// `allocator`, so the returning address must be within that region defined
    /// by the `allocator`; but we have no idea whether this pointer is virtual
    /// or physical. The caller must ensure that the pointer is used correctly.
    ///
    /// The typical use case for this is to allocate objects in low memory regions
    /// where they are identity-mapped; i.e., the virtual address equals to their
    /// physical address.
    #[verifier::external_body]
    pub fn new_zeroed_with_f(allocator: &DefaultDekoHeapAllocator, Ghost(f): Ghost<F>) -> (s: (
        Self,
        Tracked<BoxPointsTo<V>>,
    ))
        requires
            allocator.wf(),
        ensures
            s.0.wf(),
            s.1@@.pptr() === s.0@@,
            s.1@@.is_uninit(),
            s.1@@.wf(),
    {
        let (pptr, Tracked(mut pptr_perm)) = DekoPPtr::empty(allocator);

        unsafe {
            core::ptr::write_bytes(pptr.addr() as *mut u8, 0x00, core::mem::size_of::<V>());
        }

        let tracked boxed_pt = BoxPointsTo { points_to: pptr_perm };

        (Self { ptr: pptr, inv: Ghost(f) }, Tracked(boxed_pt))
    }

    /// Allocates memory on the heap and then places `x` into it.
    ///
    /// The users need to provide the allocator with an invariant function `f` that
    /// is used to verify the memory contents.
    ///
    /// Similar to `new_zeroed_with_f`, the caller must ensure that the pointer
    /// is used correctly as virtual or physical address; or the write will fail.
    #[verifier::external_body]
    pub fn new_with_f(x: V, allocator: &DefaultDekoHeapAllocator, Ghost(f): Ghost<F>) -> (s: (
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
            s.1@@.wf(),
    {
        let (b, Tracked(perm)) = Self::new_zeroed_with_f(allocator, Ghost(f));
        b.write(Tracked(&mut perm), x);

        (b, Tracked(perm))
    }

    #[inline]
    pub fn addr(&self) -> (r: u64)
        requires
            self.wf(),
        ensures
            r == self@.addr(),
    {
        self.ptr.addr() as u64
    }

    /// Consumes the box and returns the underlying pointer and permission.
    #[inline]
    pub fn into_ptr(self, Tracked(perm): Tracked<BoxPointsTo<V>>) -> (r: (
        DekoPPtr<V>,
        Tracked<DekoPointsTo<V>>,
    ))
        requires
            self.wf(),
            perm@.pptr() === self@@,
            perm@.wf(),
        ensures
            r.0 == self@,
            r.1@ == perm@,
            r.1.wf(),
    {
        (self.ptr, Tracked(perm.points_to))
    }

    #[inline]
    pub fn ptr(&self) -> (r: DekoPPtr<V>)
        requires
            self.wf(),
        ensures
            r == self@,
    {
        self.ptr
    }
}

} // verus!
#[macro_export]
macro_rules! boxed_ptr {
    ($name:ty, $alloc:expr) => {{
        let (boxed, perm) = $crate::boxed::Box::<$name>::new_zeroed($alloc);

        boxed.into_ptr(perm)
    }};
}
