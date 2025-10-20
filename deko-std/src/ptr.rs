//! Permissioned pointer types for Deko.
//!
//! This module provides safe pointer arithmetic and field access capabilities with proper
//! permission tracking, including splitting and merging permissions for sub-regions.
use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::raw_ptr::{
    self, ptr_mut_from_data, Dealloc, IsExposed, MemContents, PointsToRaw, Provenance, PtrData,
};
use vstd::simple_pptr::{PPtr, PointsTo};
use vstd::view::View;

use crate::mem::{DefaultDekoHeapAllocator, DekoBuddyAllocator, PermissionDekoMem};
use crate::prelude::*;

verus! {

pub type DekoPointsToRaw = PointsToRaw;

/// DekoPPtr (which stands for “permissioned pointer”) is a wrapper around a `PPtr` pointer to a heap-allocated V.
///
/// In order to access (read or write) the value behind the pointer, the user needs a special ghost permission token
/// `DekoPointsTo<V>`.
#[repr(C, align(8))]
pub struct DekoPPtr<V: WellFormed>(pub PPtr<V>);

pub struct DekoPointsTo<V: WellFormed> {
    /// The underlying raw pointer permission.
    points_to: raw_ptr::PointsTo<V>,
    exposed: IsExposed,
    dealloc: Option<Dealloc>,
    mem_perm: PermissionDekoMem,
}

impl<V: WellFormed> WellFormed for DekoPointsTo<V> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.is_init() ==> self.value().wf()
        &&& self.mem_wf()
    }
}

impl <V: WellFormed> DekoPointsTo<V> {
    /// Creates a placeholder if needed.
    pub uninterp spec fn null_placeholder() -> Self;

    pub axiom fn null_placeholder_ok()
        ensures
            Self::null_placeholder().wf(),
            Self::null_placeholder().is_init(),
            Self::null_placeholder().pptr().addr() == 0,
    ;
}

impl<V: WellFormed> Clone for DekoPPtr<V> {
    fn clone(&self) -> (res: Self)
        ensures
            res == *self,
    {
        DekoPPtr(self.0.clone())
    }
}

impl<V: WellFormed> Copy for DekoPPtr<V> {

}

impl<V: WellFormed> DekoPPtr<V> {
    /// Returns the CPU ID that this pointer is bound to.
    /// This is useful for ensuring that certain pointers are only accessed by specific CPU cores.
    /// For example, in a multi-core system, we might want to ensure that certain data structures
    /// are only accessed by the CPU core that owns them.
    pub uninterp spec fn bound_cpu_id(&self) -> nat;

    /// Casts (re-interpret) this pointer into a pointer of another type `T`.
    ///
    /// The trait must be implemented between `V` and `T` to ensure that the cast
    /// is (semantically) valid.
    ///
    /// Since this function does not explicitly creates/consumes any permission tokens, it is safe to use
    /// this function to create multiple aliases to the same memory location.
    #[inline]
    pub fn cast_into<T>(&self) -> (r: DekoPPtr<T>) where V: SafeCastInto<T>, T: WellFormed + Sized
        ensures
            r.addr() == self.addr(),
    {
        DekoPPtr(PPtr(self.addr(), core::marker::PhantomData))
    }

    /// Similar to [`from_raw_uninit`] but this _assumes_ the underlying memory is properly initialized
    /// with some value `v` so that accessing this memory should be fine; however, note that this is
    /// _only_ valid for values that do not change.
    #[inline(always)]
    #[verifier::external_body]
    pub unsafe fn from_raw_init(addr: u64) -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.is_init(),
            pt.1@.wf(),
        opens_invariants none
    {
        let (pptr, Tracked(perm)) = Self::from_raw_uninit(addr);

        (pptr, Tracked(perm))
    }

    /// Casts a raw address into a `DekoPPtr<V>`.
    ///
    /// This is extremely unsafe as it does not check whether the address is valid or not; however, this
    /// functionality is indeed useful for some low-level operations. For example, for heap allocations,
    /// we have to manage the free lists but as we do not have system-wide allocators, we have to directly
    /// cast these addresses into `DekoPPtr<V>`s from .bss.
    ///
    /// This is will create possibly multiple alias to the same memory location.
    ///
    /// Also note that we assume the address is valid and the memory is _uninitialized_.
    #[inline(always)]
    #[verifier::external_body]
    pub unsafe fn from_raw_uninit(addr: u64) -> (pt: (Self, Tracked<DekoPointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0@,
            pt.1@.is_uninit(),
            pt.1@.wf(),
            pt.0.addr() == addr as usize,
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
            perm.wf(),
        ensures
            *v == perm.value(),
            v.wf(),
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
    pub open spec fn spec_addr(p: DekoPPtr<V>) -> usize {
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
            old(perm).wf(),
            v.wf(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(v),
            perm.wf(),
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
            v.wf(),
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

    /// Modifies the value behind the pointer in place using a closure that operates on the raw pointer.
    ///
    /// This function provides a way to perform in-place modifications of the value stored at the memory
    /// location pointed to by this pointer. It temporarily transfers ownership of the permission token
    /// to the function, executes the provided closure with a raw pointer to the memory, and then
    /// returns the permission token.
    ///
    /// # Safety Analysis
    ///
    /// This function contains several important safety considerations:
    ///
    /// ## Permission Transfer Safety
    /// - **Exclusive Access**: The function takes ownership of the `DekoPointsTo<V>` permission token,
    ///   ensuring exclusive access to the memory during the operation.
    /// - **Temporal Safety**: During the execution of closure `f`, the caller cannot access the memory
    ///   through any other means, preventing data races and use-after-free bugs.
    /// - **Permission Reconstruction**: The permission token is reconstructed and returned, maintaining
    ///   the ownership invariants of the permission system.
    ///
    /// ## Raw Pointer Safety
    /// - **Initialized Memory**: The function requires that the memory is initialized (`perm.is_init()`),
    ///   ensuring that the closure operates on valid data.
    /// - **Closure Constraints**: The closure `f` must satisfy specific preconditions and postconditions
    ///   that are verified at compile time through the Verus specification system.
    /// - **No Implicit Dereference**: Since Verus doesn't support implicit mutable dereferencing,
    ///   this function provides a controlled way to perform mutable operations.
    ///
    /// ## Memory Layout Preservation
    /// - **Pointer Stability**: The function ensures that the pointer address remains unchanged
    ///   (`r@.ptr() == perm.ptr()`), preventing memory layout corruption.
    /// - **Type Preservation**: The operation maintains the type `V`, ensuring type safety.
    ///
    /// # Type Parameters
    ///
    /// * `V` - The type of the value stored at the memory location. Must implement `WellFormed`.
    ///
    /// # Parameters
    ///
    /// * `perm` - The permission token that grants exclusive access to the memory location.
    ///   This token is consumed by the function and reconstructed in the return value.
    /// * `f` - A closure that takes a mutable raw pointer to the memory location and performs
    ///   the desired modifications. The closure must satisfy the specified preconditions and
    ///   postconditions.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// // Example: Incrementing a counter stored in heap memory
    /// let (ptr, mut perm) = DekoPPtr::<u64>::new(42, &allocator);
    ///
    /// let perm = ptr.update_in_place(Tracked(perm), |raw_ptr| {
    ///     unsafe {
    ///         *raw_ptr += 1;
    ///     }
    /// });
    ///
    /// // The value is now 43
    /// ```
    ///
    /// ```rust,ignore
    /// // Example: Modifying a struct field
    /// struct Point { x: i32, y: i32 }
    /// let (ptr, mut perm) = DekoPPtr::<Point>::new(Point { x: 10, y: 20 }, &allocator);
    ///
    /// let perm = ptr.update_in_place(Tracked(perm), |raw_ptr| {
    ///     unsafe {
    ///         (*raw_ptr).x = 100;
    ///     }
    /// });
    /// ```
    pub fn update_in_place(
        &self,
        Tracked(perm): Tracked<DekoPointsTo<V>>,
        f: impl FnOnce(*mut V),
    ) -> (r: Tracked<DekoPointsTo<V>>)
        requires
            perm.pptr() == self@,
            perm.wf(),
            perm.is_init(),
            f.requires((perm.ptr(),)),
        ensures
            r@.pptr() == self@,
            r@.wf(),
            r@.ptr() == perm.ptr(),
            f.ensures((r@.ptr(),), ()),
    {
        proof {
            use_type_invariant(&perm);
        }
        let ptr: *mut V = vstd::raw_ptr::with_exposed_provenance(self.0.0, Tracked(perm.exposed));

        f(ptr);

        // reconstruct the permission token
        Tracked(perm)
    }

    /// Reinterprets the memory location pointed to by this pointer as a different type `T` and writes a value of type `T`.
    ///
    /// This function performs a type reinterpretation at the memory level, allowing you to write a value of type `T`
    /// to memory that was originally allocated for type `V`. This is a powerful but potentially dangerous operation
    /// that requires careful consideration of memory layout, alignment, and type safety.
    ///
    /// # Safety Analysis
    ///
    /// This function is marked with `#[verifier::external_body]` and contains several safety mechanisms:
    ///
    /// ## Type Safety Constraints
    /// - **SafeCastInto Trait**: The source type `V` must implement `SafeCastInto<T>` for the target type `T`.
    ///   This trait ensures that the cast is semantically valid and preserves memory layout invariants.
    /// - **WellFormed Requirement**: Both `V` and `T` must implement `WellFormed`, ensuring they have valid
    ///   internal structure and can be safely manipulated.
    /// - **Cast Validation**: The precondition `<V as SafeCastInto<T>>::cast_valid()` must be true,
    ///   providing a specification-level guarantee that the cast is valid.
    ///
    /// ## Memory Layout Safety
    /// - The `SafeCastInto` trait includes a `cast_preserves_layout()` proof function that ensures
    ///   `size_of::<V>() == size_of::<T>()` and `align_of::<V>() == align_of::<T>()`.
    /// - This prevents memory corruption that could occur from size or alignment mismatches.
    ///
    /// ## Permission System Safety
    /// - Requires exclusive mutable access to the `DekoPointsTo<V>` permission token.
    /// - The permission system ensures memory safety by tracking ownership and preventing data races.
    /// - The function maintains the pointer address (`perm.pptr()`) while updating the memory contents.
    ///
    /// ## Potential Safety Concerns
    /// - **Type Punning**: This function essentially performs type punning, which can be unsafe if the
    ///   bit patterns of `V` and `T` have different _semantic_ meanings. You may need more proof for it
    ///   but this function does not handle this.
    /// - **Drop Semantics**: If `V` had a custom `Drop` implementation, it will not be called when
    ///   reinterpreting to `T`. This could lead to resource leaks if not handled properly.
    /// - **Invariant Violations**: Type-specific invariants of `V` may not hold for `T`, even if
    ///   the memory layout is compatible.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The target type to reinterpret the memory as. Must implement `WellFormed` and `Sized`.
    ///
    /// # Parameters
    ///
    /// * `perm` - A tracked mutable reference to the permission token that grants access to the memory.
    ///   This token is updated to reflect the new type `T` and the written value.
    /// * `t` - The value of type `T` to write to the memory location.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// // Example: Reinterpreting a u64 as two u32s (hypothetical implementation)
    /// let (ptr, mut perm) = DekoPPtr::<u64>::new(0x1234567890ABCDEF, &allocator);
    ///
    /// // Assuming U64ToU32Array implements SafeCastInto<[u32; 2]>
    /// ptr.reinterpret_write(Tracked(&mut perm), [0x90ABCDEF_u32, 0x12345678_u32]);
    /// ```
    ///
    /// # See Also
    ///
    /// * [`SafeCastInto`] - The trait that defines valid casting relationships
    /// * [`cast_into`] - For safe pointer type casting without writing
    /// * [`write`] - For writing values of the same type
    /// * [`put`] - For writing to uninitialized memory of the same type
    #[verifier::external_body]
    pub fn reinterpret_write<T>(&self, Tracked(perm): Tracked<&mut DekoPointsTo<V>>, t: T) where
        V: SafeCastInto<T>,
        T: WellFormed + Sized,

        requires
            old(perm).pptr() == self@,
            old(perm).wf(),
            old(perm).is_init(),
            old(perm).value().cast_valid(),
            t.wf(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.wf(),
            perm.mem_contents() matches MemContents::Init(v) ==> {
                <V as SafeCastInto<T>>::cast_into(v) == t
            },
        opens_invariants none
        no_unwind
    {
        let Tracked(mut perm) = Tracked::<DekoPointsTo<T>>::assume_new();
        let new_ptr = DekoPPtr::<T>(PPtr::<T>(self.addr(), core::marker::PhantomData::<T>));
        new_ptr.write(Tracked(&mut perm), t);
    }

    /// Reinterprets the memory location pointed to by this pointer as a different type `T` and returns a reference to it.
    ///
    /// This function performs a type reinterpretation at the memory level, allowing you to access a value of type `T`
    /// from memory that was originally allocated for type `V`. This is a powerful but potentially dangerous operation
    /// that requires careful consideration of memory layout, alignment, and type safety.
    ///
    /// # Safety Analysis
    ///
    /// This function is marked with `#[verifier::external_body]` and contains several safety mechanisms:
    ///
    /// ## Type Safety Constraints
    /// - **SafeCastInto Trait**: The source type `V` must implement `SafeCastInto<T>` for the target type `T`.
    ///   This trait ensures that the cast is semantically valid and preserves memory layout invariants.
    /// - **WellFormed Requirement**: Both `V` and `T` must implement `WellFormed`, ensuring they have valid
    ///   internal structure and can be safely manipulated.
    /// - **Cast Validation**: The precondition `<V as SafeCastInto<T>>::cast_valid()` must be true,
    ///   providing a specification-level guarantee that the cast is valid.
    ///
    /// ## Memory Layout Safety
    /// - The `SafeCastInto` trait includes a `cast_preserves_layout()` proof function that ensures
    ///   `size_of::<V>() == size_of::<T>()` and `align_of::<V>() == align_of::<T>()`.
    /// - This prevents memory corruption that could occur from size or alignment mismatches.
    ///
    /// ## Permission System Safety
    /// - Requires read access to the `DekoPointsTo<V>` permission token.
    /// - The permission system ensures memory safety by tracking ownership and preventing data races.
    /// - The function maintains the pointer address while providing access to the memory contents.
    /// - The lifetime of the returned reference is tied to the permission token's lifetime.
    ///
    /// ## Potential Safety Concerns
    /// - **Type Punning**: This function essentially performs type punning, which can be unsafe if the
    ///   bit patterns of `V` and `T` have different _semantic_ meanings. The caller must ensure that
    ///   the reinterpretation is semantically valid.
    /// - **Invariant Violations**: Type-specific invariants of `V` may not hold for `T`, even if
    ///   the memory layout is compatible. The caller must ensure the accessed value satisfies `T`'s invariants.
    /// - **Reference Validity**: The returned reference is only valid as long as the permission token
    ///   remains valid and no mutable operations are performed on the memory.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The target type to reinterpret the memory as. Must implement `WellFormed` and `Sized`.
    ///
    /// # Parameters
    ///
    /// * `perm` - A tracked reference to the permission token that grants access to the memory.
    ///
    /// # Returns
    ///
    /// * A reference to the memory reinterpreted as type `T`. The lifetime is tied to the permission token.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// // Example: Reinterpreting a [u32; 2] as a u64
    /// let (ptr, perm) = DekoPPtr::<[u32; 2]>::new([0x12345678, 0x90ABCDEF], &allocator);
    ///
    /// // Assuming [u32; 2] implements SafeCastInto<u64>
    /// let value_ref: &u64 = ptr.reinterpret_read(Tracked(&perm));
    /// // *value_ref would be 0x90ABCDEF12345678 (depending on endianness)
    /// ```
    ///
    /// ```rust,ignore
    /// // Example: Reinterpreting a struct as a byte array
    /// #[repr(C)]
    /// struct Point { x: f32, y: f32 }
    /// let (ptr, perm) = DekoPPtr::<Point>::new(Point { x: 1.0, y: 2.0 }, &allocator);
    ///
    /// // Assuming Point implements SafeCastInto<[u8; 8]>
    /// let bytes_ref: &[u8; 8] = ptr.reinterpret_read(Tracked(&perm));
    /// ```
    ///
    /// # See Also
    ///
    /// * [`SafeCastInto`] - The trait that defines valid casting relationships
    /// * [`reinterpret_write`] - For writing values as a different type
    /// * [`cast_into`] - For safe pointer type casting without reading
    /// * [`borrow`] - For reading values of the same type
    #[verifier::external_body]
    pub fn reinterpret_read<'a, T>(&self, Tracked(perm): Tracked<&'a DekoPointsTo<V>>) -> (r:
        &'a T) where V: SafeCastInto<T>, T: WellFormed + Sized
        requires
            perm.pptr() == self@,
            perm.wf(),
            perm.is_init(),
            perm.value().cast_valid(),
        ensures
            *r == <V as SafeCastInto<T>>::cast_into(perm.value()),
            r.wf(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *const V = vstd::raw_ptr::with_exposed_provenance(self.0.0, Tracked(perm.exposed));
        unsafe {
            // Safe because:
            // 1. We have verified the cast is valid through SafeCastInto
            // 2. Memory layout is preserved (same size and alignment)
            // 3. We have read permission through the DekoPointsTo token
            // 4. The lifetime is tied to the permission token
            &*(ptr as *const T)
        }
    }
}

impl<V: WellFormed> DekoPointsTo<V> {
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

    #[verifier::inline]
    pub open spec fn dptr(&self) -> DekoPPtr<V> {
        DekoPPtr(self.pptr())
    }

    pub closed spec fn ptr(&self) -> *mut V {
        self.points_to.ptr()
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
        &&& self.wf()
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
impl<T: WellFormed> View for DekoPPtr<T> {
    type V = PPtr<T>;

    open spec fn view(&self) -> Self::V {
        self.0
    }
}

} // verus!
#[cfg(feature = "alloc")]
verus! {

impl<V: WellFormed> DekoPPtr<V> {
    /// Constructs a possibly uninitialized `DekoPPtr<V>`.
    ///
    /// Please be extra careful that this function returns a pointer
    /// (physical address).
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
            v.wf(),
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
