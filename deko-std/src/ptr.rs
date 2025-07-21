use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::raw_ptr::{
    self, ptr_mut_from_data, Dealloc, IsExposed, MemContents, PointsToRaw, Provenance, PtrData,
};
use vstd::simple_pptr::{PPtr, PointsTo};
use vstd::view::View;

use crate::mem::{DefaultDekoHeapAllocator, DekoHeapAllocator, PermissionDekoMem};
use crate::prelude::*;

verus! {

/// DekoPPtr (which stands for “permissioned pointer”) is a wrapper around a `PPtr` pointer to a heap-allocated V.
///
/// In order to access (read or write) the value behind the pointer, the user needs a special ghost permission token
/// `DekoPointsTo<V>`.
///
/// TODO: Add a permission memory token or some "privilege layer" checking.
pub struct DekoPPtr<V>(PPtr<V>);

pub struct DekoPointsTo<V> {
    points_to: raw_ptr::PointsTo<V>,
    exposed: IsExposed,
    dealloc: Option<Dealloc>,
    mem_perm: PermissionDekoMem,
}

impl<V> WellFormed for DekoPointsTo<V> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        self.mem_wf()
    }
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
    /// Casts a raw address into a `DekoPPtr<V>`.
    ///
    /// This is extremely unsafe as it does not check whether the address is valid or not; however, this
    /// functionality is indeed useful for some low-level operations. For example, for heap allocations,
    /// we have to manage the free lists but as we do not have system-wide allocators, we have to directly
    /// cast these addresses into `DekoPPtr<V>`s from .bss.
    ///
    /// Also note that we assume the address is valid and the memory is _uninitialized_.
    #[inline(always)]
    #[verifier::external_body]
    pub unsafe fn from_raw_uninit(addr: u64) -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.is_uninit(),
            pt.1@.wf(),
    // We don't put dealloc here as we do't "own" it.

        opens_invariants none
    {
        let Tracked(points_to_raw) = Tracked::<PointsToRaw>::assume_new();
        let Tracked(dealloc) = Tracked::<Dealloc>::assume_new();

        let Tracked(exposed) = vstd::raw_ptr::expose_provenance::<u8>(addr as _);
        let tracked points_to = points_to_raw.into_typed::<V>(addr as usize);

        let tracked pt = DekoPointsTo {
            points_to,
            exposed,
            dealloc: Some(dealloc),
            mem_perm: PermissionDekoMem::Foo,
        };

        let pptr = DekoPPtr(PPtr(addr as usize, PhantomData));

        (pptr, Tracked(pt))
    }

    /// Try to borrow this pointer.
    #[inline(always)]
    pub fn borrow<'a>(self, Tracked(perm): Tracked<&'a DekoPointsTo<V>>) -> (v: &'a V)
        requires
            perm.pptr() == self@,
            perm.is_init(),
            perm.mem_wf(),
        ensures
            *v == perm.value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = vstd::raw_ptr::with_exposed_provenance(self.0.0, Tracked(perm.exposed));
        vstd::raw_ptr::ptr_ref(ptr, Tracked(&perm.points_to))
    }

    /// Use `addr()` instead
    pub closed spec fn spec_addr(p: DekoPPtr<V>) -> usize {
        p@.addr()
    }

    /// Moves v out of the location pointed to by the pointer self and returns it.
    ///
    /// Requires the memory to be initialized, and leaves it uninitialized.
    #[inline(always)]
    pub fn take(self, Tracked(perm): Tracked<&mut DekoPointsTo<V>>) -> (v: V)
        requires
            old(perm).pptr() == self@,
            old(perm).is_init(),
            old(perm).mem_wf(),
            old(perm).wf(),
        ensures
            perm.pptr() == old(perm).pptr(),  // the pointer remains the same
            v == old(perm).value(),
            perm.is_uninit(),
            perm.mem_wf(),
            perm.wf(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = vstd::raw_ptr::with_exposed_provenance(self.0.0, Tracked(perm.exposed));
        vstd::raw_ptr::ptr_mut_read(ptr, Tracked(&mut perm.points_to))
    }

    /// Cast a pointer to an integer.
    #[inline(always)]
    #[verifier::when_used_as_spec(spec_addr)]
    pub fn addr(self) -> (u: usize)
        ensures
            u == Self::spec_addr(self),
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

    #[inline(always)]
    pub fn write(&self, Tracked(perm): Tracked<&mut DekoPointsTo<V>>, v: V)
        requires
            old(perm).pptr() == self@,
            old(perm).wf(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(v),
            perm.wf(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
            perm.leak_contents();
        }
        self.put(Tracked(perm), v);
    }
}

impl<V> DekoPointsTo<V> {
    /// "Forgets" about the value stored behind the pointer.
    /// Updates the `PointsTo` value to [`MemContents::Uninit`](MemContents::Uninit).
    /// Note that this is a `proof` function, i.e., it is operationally a no-op in executable code.
    pub proof fn leak_contents(tracked &mut self)
        ensures
            self.pptr() == old(self).pptr(),
            self.is_uninit(),
    {
        use_type_invariant(&*self);
        self.points_to.leak_contents();
    }

    #[verifier::inline]
    pub open spec fn pptr(&self) -> PPtr<V> {
        PPtr(self.addr(), PhantomData)
    }

    pub closed spec fn mem_wf(&self) -> bool {
        self.mem_perm.wf()
    }

    pub closed spec fn addr(self) -> usize {
        self.points_to.ptr().addr()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
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

    pub open spec fn value(&self) -> V {
        self.mem_contents().value()
    }
}

// Quick way to invoke inner's specs and methods.
impl<T> View for DekoPPtr<T> {
    type V = PPtr<T>;

    closed spec fn view(&self) -> Self::V {
        self.0
    }
}

} // verus!
#[cfg(feature = "alloc")]
verus! {

impl<V> DekoPPtr<V> {
    /// Constructs a possibly uninitialized `DekoPPtr<V>`.
    pub fn empty(allocator: &DefaultDekoHeapAllocator) -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        requires
            allocator.wf(),
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.is_uninit(),
        opens_invariants none
    {
        vstd::layout::layout_for_type_is_valid::<V>();

        match core::mem::size_of::<V>() {
            v if v != 0 => {
                let (p, Tracked(points_to_raw), Tracked(dealloc)) = allocator.alloc(
                    core::mem::size_of::<V>(),
                    core::mem::align_of::<V>(),
                );
                let Tracked(exposed) = vstd::raw_ptr::expose_provenance::<u8>(p);
                let tracked points_to = points_to_raw.into_typed::<V>(p.addr());
                proof {
                    points_to.is_nonnull();
                }

                let tracked pt = DekoPointsTo {
                    points_to,
                    exposed,
                    dealloc: Some(dealloc),
                    mem_perm: PermissionDekoMem::Foo,
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
                    mem_perm: PermissionDekoMem::Foo,
                };
                let pptr = DekoPPtr(PPtr(p, PhantomData));

                (pptr, Tracked(pt))
            },
        }
    }

    /// Allocates heap memory for type `V`, leaving it initialized with the given value `v`.
    pub fn new(v: V, allocator: &DefaultDekoHeapAllocator) -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        requires
            allocator.wf(),
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.mem_contents() == MemContents::Init(v),
            pt.1@.mem_wf(),
        opens_invariants none
    {
        let (p, Tracked(mut pt)) = Self::empty(allocator);
        p.put(Tracked(&mut pt), v);
        (p, Tracked(pt))
    }

    /// De-allocates the memory pointed to by `self`.
    ///
    /// # Safety
    ///
    /// This function call added the explicit pre-condition `perm.is_uninit()` to ensure that
    /// target itself has called its clenaup logics. This function cleans up the memory taken
    /// by that tyep `V` but DOES NOT call `V::drop()`.
    ///
    /// To properly take care of the memory, you should call move `V` out of the pointer and
    /// then discard `V` elsewhere.
    pub fn drop(self, Tracked(perm): Tracked<DekoPointsTo<V>>, allocator: &DefaultDekoHeapAllocator)
        requires
            (perm).pptr() == self@,
            (perm).is_uninit(),
            (perm).mem_wf(),
            allocator.wf(),
        ensures
            perm.mem_contents() == MemContents::Uninit::<V>,
        opens_invariants none
    {
        proof {
            use_type_invariant(&perm);
        }

        let size = core::mem::size_of::<V>();
        let align = core::mem::align_of::<V>();

        if size > 0 {
            let tracked dealloc = perm.dealloc.tracked_unwrap();
            let tracked raw = perm.points_to.into_raw();
            let tracked exposed = perm.exposed;
            let ptr = vstd::raw_ptr::with_exposed_provenance(self.0.0, Tracked(exposed));
            allocator.dealloc(ptr, size, align, Tracked(raw), Tracked(dealloc));
        } else {
            // for ZST the memory is not allocated so it is safe to assume
            // that the memory is uninitialized.
            proof {
                assume(perm.mem_contents() matches MemContents::Uninit::<V>);
            }
        }

    }
}

} // verus!
