use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::raw_ptr::{
    self, ptr_mut_from_data, Dealloc, IsExposed, MemContents, PointsToRaw, Provenance, PtrData,
};
use vstd::simple_pptr::{PPtr, PointsTo};
use vstd::view::View;

use crate::mem::PermissionDekoMem;
use crate::prelude::*;

verus! {

/// DekoPPtr (which stands for “permissioned pointer”) is a wrapper around a `PPtr` pointer to a heap-allocated V.
///
/// In order to access (read or write) the value behind the pointer, the user needs a special ghost permission token
/// `DekoPointsTo<V>`.
pub struct DekoPPtr<V>(pub PPtr<V>);

pub struct DekoPointsTo<V> {
    points_to: raw_ptr::PointsTo<V>,
    exposed: IsExposed,
    dealloc: Option<Dealloc>,
    permission: PermissionDekoMem,
}

impl<V> Clone for DekoPPtr<V> {
    fn clone(&self) -> (res: Self)
        ensures
            res == *self,
    {
        DekoPPtr(self.0.clone())
    }
}

impl<V> Copy for DekoPPtr<V> {

}

impl<V> DekoPPtr<V> {
    /// Use `addr()` instead
    #[verifier::inline]
    pub open spec fn spec_addr(p: DekoPPtr<V>) -> usize {
        p.0.addr()
    }

    /// Cast a pointer to an integer.
    #[inline(always)]
    #[verifier::when_used_as_spec(spec_addr)]
    pub fn addr(self) -> (u: usize)
        ensures
            u == self@.addr(),
    {
        self.0.addr()
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.mem_contents()`
    /// from `MemContents::Uninit` to `MemContents::Init(v)`.
    #[inline(always)]
    pub fn put(self, Tracked(perm): Tracked<&mut DekoPointsTo<V>>, v: V)
        requires
            old(perm).pptr() == self@,
            old(perm).mem_contents() == MemContents::Uninit::<V>,
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(v),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = vstd::raw_ptr::with_exposed_provenance(self.0.0, Tracked(perm.exposed));
        vstd::raw_ptr::ptr_mut_write(ptr, Tracked(&mut perm.points_to), v);
    }
}

impl<V> DekoPointsTo<V> {
    #[verifier::inline]
    pub open spec fn pptr(&self) -> PPtr<V> {
        PPtr(self.addr(), PhantomData)
    }

    pub closed spec fn addr(self) -> usize {
        self.points_to.ptr().addr()
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        &&& self.points_to.ptr()@.provenance == self.exposed.provenance()
        &&& match self.dealloc {
            Some(dealloc) => {
                &&& dealloc.addr() == self.points_to.ptr().addr()
                &&& dealloc.size() == size_of::<V>()
                &&& dealloc.align() == align_of::<V>()
                &&& dealloc.provenance() == self.points_to.ptr()@.provenance
                &&& size_of::<V>() > 0
            },
            None => { size_of::<V>() == 0 },
        }
        &&& self.points_to.ptr().addr() != 0
    }

    pub closed spec fn mem_contents(&self) -> MemContents<V> {
        self.points_to.opt_value()
    }

    pub open spec fn is_uninit(&self) -> bool {
        self.mem_contents().is_uninit()
    }

    pub open spec fn is_init(&self) -> bool {
        self.mem_contents().is_init()
    }
}

// Quick way to invoke inner's specs and methods.
impl<T> View for DekoPPtr<T> {
    type V = PPtr<T>;

    open spec fn view(&self) -> Self::V {
        self.0
    }
}

} // verus!
#[cfg(feature = "alloc")]
verus! {

impl<V> DekoPPtr<V> {
    /// Constructs a possibly uninitialized `DekoPPtr<V>`.
    pub fn empty() -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.is_uninit(),
        opens_invariants none
    {
        vstd::layout::layout_for_type_is_valid::<V>();

        match core::mem::size_of::<V>() {
            v if v != 0 => {
                let (p, Tracked(points_to_raw), Tracked(dealloc)) = crate::mem::allocate(
                    core::mem::size_of::<V>(),
                    core::mem::align_of::<V>(),
                );
                let Tracked(exposed) = vstd::raw_ptr::expose_provenance(p);
                let tracked points_to = points_to_raw.into_typed::<V>(p.addr());
                proof {
                    points_to.is_nonnull();
                }

                let tracked pt = DekoPointsTo {
                    points_to,
                    exposed,
                    dealloc: Some(dealloc),
                    permission: PermissionDekoMem::Foo,
                };
                let pptr = DekoPPtr(PPtr(p as usize, PhantomData));

                (pptr, Tracked(pt))
            },
            _ => {
                let p = core::mem::align_of::<V>();
                assert(p % p == 0) by (nonlinear_arith)
                    requires
                        p != 0,
                ;
                let tracked emp = PointsToRaw::empty(Provenance::null());
                let tracked points_to = emp.into_typed(p);
                let tracked pt = DekoPointsTo {
                    points_to,
                    exposed: IsExposed::null(),
                    dealloc: None,
                    permission: PermissionDekoMem::Foo,
                };
                let pptr = DekoPPtr(PPtr(p, PhantomData));

                (pptr, Tracked(pt))
            },
        }
    }

    /// Allocates heap memory for type `V`, leaving it initialized with the given value `v`.
    pub fn new(v: V) -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.mem_contents() == MemContents::Init(v),
        opens_invariants none
    {
        let (p, Tracked(mut pt)) = Self::empty();
        p.put(Tracked(&mut pt), v);
        (p, Tracked(pt))
    }
}

} // verus!
