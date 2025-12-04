use vstd::prelude::*;

use crate::ptr::DekoPPtr;
use crate::WellFormed;

verus! {

/// A raw pointer type which can be safely shared between threads.
///
/// This type has the same size and bit validity as a *mut T (see
/// [`DekoPPtr`] and [`vstd::simple_pptr::PPtr`]) with only [`Tracked`]
/// and [`core::marker::PhantomData`] added for verification purposes.
///
/// Note: This type is only available on platforms that support atomic
/// loads and stores of pointers. Its size depends on the target pointer’s size.
#[repr(transparent)]
pub struct AtomicPtr<V: WellFormed> {
    ptr: DekoPPtr<V>,
}

#[verifier::external]
unsafe impl<V: WellFormed> Send for AtomicPtr<V> {

}

#[verifier::external]
unsafe impl<V: WellFormed> Sync for AtomicPtr<V> {

}

impl<V: WellFormed> AtomicPtr<V> {
    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value gaurantees that no other threads
    /// are concurrently accessing the atomic data.
    #[verifier::atomic]
    pub const fn into_inner(self) -> (r: DekoPPtr<V>) {
        self.ptr
    }
}

} // verus!
