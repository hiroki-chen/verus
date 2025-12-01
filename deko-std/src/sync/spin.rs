//! Runtime Permission-Tracking Spinlock Implementation
//!
//! This module provides a spinlock synchronization primitive that incorporates
//! runtime permission tracking. Unlike traditional spinlocks that only provide
//! mutual exclusion, this implementation maintains and enforces access permissions
//! dynamically, creating temporary read/write permissions as needed without
//! transferring ownership of the protected data.
//!
//! # Overview
//!
//! The permission-tracking spinlock extends basic mutual exclusion with a
//! sophisticated permission model that:
//!
//! - **Runtime Permission Validation**: Validates access permissions at lock
//!   acquisition time, ensuring that only authorized operations proceed
//! - **Temporary Permission Creation**: Generates temporary read/write permissions
//!   for the duration of the lock, allowing safe access without ownership transfer
//! - **Non-Owning Access Control**: Provides controlled access to protected data
//!   while maintaining the original ownership structure
//! - **Low-Level Synchronization**: Uses busy-waiting spinlock semantics suitable
//!   for kernel-space and interrupt contexts where blocking is not permitted
//!
//! # Permission Model
//!
//! The permission tracking system distinguishes between different types of access:
//!
//! - **Read Permissions**: Allow read-only access to the protected data
//! - **Write Permissions**: Allow mutable access with modification rights
//! - **Temporary Grants**: Short-lived permissions that exist only during lock hold
//!
//! These permissions are validated and managed at runtime, providing fine-grained
//! control over how different parts of the system can interact with shared resources.
//!
//! # Safety and Performance
//!
//! The spinlock implementation maintains safety through:
//!
//! - **Permission Validation**: Runtime checks ensure only authorized access
//! - **Atomic Operations**: Uses hardware atomic primitives for lock state
//! - **Interrupt Safety**: Compatible with interrupt handling and critical sections
//!
//! Furthermore, runtime checking means that there is NO compile-time gaurantees
//! of properties in Verus. For example,
//!
//! ```rust
//!     let a = B.modify(a <- 5); // where B is a SpinLock
//!     proof! {
//!         assert(a == 5);
//!     }
//! ```
//!
//! this assertion will simply fail because other cores may modify the data
//! between the lock and the read; thus:
//!
//! ```rust
//!     let a = B.modify(a <- 5); // where B is a SpinLock
//!     if a == 5 {
//!         proof! {
//!             // this will pass
//!             assert(a == 5);
//!         }
//!     }
//! ```
use core::borrow::{Borrow, BorrowMut};
use core::cell::UnsafeCell;

use vstd::atomic::{PAtomicBool, PermissionBool};
use vstd::cell::PCell;
use vstd::invariant;
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

use crate::wf::WellFormed;

verus! {

pub assume_specification[ core::hint::spin_loop ]()
;

/// Maximum number of attempts to acquire the spinlock.
const MAX_ATTEMPT: usize = 100_0000;

/// Specifies how permission grants the access to the underlying data protected by the spinlock.
///
/// # Example
///
/// ```rust,norun
/// impl SpinLockPermission<DekoPPtr<MyData>> for vstd::simple_pptr:PointsTo<MyData> {
///     open spec fn wf_with(&self, value: &DekoPPtr<MyData>) -> bool {
///         &&& self.pptr() == value@
///         &&& self.wf()
///     }
/// }
/// ```
pub trait SpinPermission<'a, T: ?Sized>: WellFormed + Sized {
    /// Basic specification of how this permission makes the underlying data well-formed.
    spec fn spin_wf_with(&self, value: &T) -> bool;

    /// Specifies how this permission allows reading the underlying data.
    open spec fn spin_read_wf_with(&self, value: &T) -> bool {
        self.spin_wf_with(value)
    }

    /// Specifies how this permission allows writing to the underlying data.
    open spec fn spin_write_wf_with(&self, value: &T) -> bool {
        self.spin_wf_with(value)
    }

    /// How a new permission is created when the spinlock is acquired.
    proof fn create_new(val: &T) -> (tracked r: Self)
        ensures
            r.spin_wf_with(val),
    ;
}

/// A wrapper to bypass the Verus restriction on using `UnsafeCell` directly in `SpinLock`.
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct SpinCell<T: ?Sized>(UnsafeCell<T>);

impl<T: ?Sized> SpinCell<T> {
    /// We want `?Szied` so this function is to bypass the
    /// type checker.
    pub uninterp spec fn into_inner_spec(&self) -> &T;
}

impl<T> SpinCell<T> {
    #[verifier::external_body]
    pub const fn new(value: T) -> Self {
        SpinCell(UnsafeCell::new(value))
    }

    #[verifier::external_body]
    pub fn into_inner(self) -> (r: T)
        ensures
            r == self.into_inner_spec(),
    {
        self.0.into_inner()
    }
}

/// A type alias for a spinlock that disables interrupts during critical sections.
pub type SpinLockNoIrq<T, P> = SpinLock<T, SpinNoIrq, P>;

/// A trait for implementing spinlock synchronization primitives with interrupt safety.
///
/// This trait provides the essential interface for spinlock implementations that
/// require interrupt disabling during critical sections. It handles the lock
/// acquisition and release protocol while ensuring atomic operations and
/// preventing interrupt-based preemption.
///
/// # Associated Types
///
/// * `GuardData` - Data associated with the lock guard, typically containing
///   interrupt state or permission information that must be restored on unlock.
///
/// # Safety
///
/// Implementations must ensure:
/// - `lock_prologue()` optional function that is called before acquiring the lock.
///    It typically disables interrupts.
/// - `lock_epilogue()` function that is called after releasing the lock. It typically restores
///   the interrupt state saved during `lock_prologue()`.
pub trait Spin: Sized {
    type GuardData;

    spec fn obeys_spin_specs() -> bool;

    spec fn new_spec() -> Self;

    fn new() -> (r: Self)
        ensures
            Self::obeys_spin_specs() ==> r == Self::new_spec(),
    ;

    /// Disables interrupt when you tries to obtain the lock.
    /// Kernel-side locks, such as `SpinLock`s do indeed block interrupts (on that processor core) to ensure that
    /// other processes/threads do not get scheduled during this process.
    fn lock_prologue() -> Self::GuardData;

    /// Releases when `MutexGuard` drops itself.
    fn lock_epilogue(&self);
}

pub struct SpinNoIrq;

/// Data associated with the `SpinNoIrq` lock guard;
/// this is the interrupt flags before acquiring the lock.
pub struct SpinFlags(pub u64);

#[verus_verify]
impl SpinFlags {
    /// Creates a new `SpinFlags` with default interrupt flags.
    #[verifier::external_body]
    pub fn new() -> Self {
        vstd::vpanic!("todo")
    }
}

impl Drop for SpinFlags {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        // Restore the interrupt flags here.
        // This is a no-op in the verifier.
        vstd::vpanic!("todo")
    }
}

impl Spin for SpinNoIrq {
    type GuardData = SpinFlags;

    open spec fn obeys_spin_specs() -> bool {
        true
    }

    open spec fn new_spec() -> Self {
        SpinNoIrq
    }

    fn new() -> (r: Self)
        ensures
            r == Self::new_spec(),
    {
        SpinNoIrq
    }

    fn lock_prologue() -> Self::GuardData {
        Self::GuardData::new()
    }

    fn lock_epilogue(&self) {
        // Self::GuardData will be dropped automatically
        // and restore the interrupt flags. So no action is needed here.
    }
}

/// A guard that releases the spinlock when dropped.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(P)]
pub struct SpinLockGuard<'a, T: ?Sized, S: Spin, P> {
    /// The id of this guard.
    pub id: Ghost<int>,
    /// The lock it is holding.
    pub lock: &'a SpinLock<T, S, P>,
    /// permission to the underlying data.
    /// The guard data associated with the spin strategy.
    pub data: S::GuardData,
    /// Permission to the underlying data.
    pub perm: Tracked<P>,
}

impl<'a, T: WellFormed, S: Spin, P: SpinPermission<'a, T>> WellFormed for SpinLockGuard<
    'a,
    T,
    S,
    P,
> {
    open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.id == self.lock.id
        &&& self.perm@.spin_wf_with(&self.lock.data.into_inner_spec())
    }
}

impl<'a, T: ?Sized, S: Spin, P> Drop for SpinLockGuard<'a, T, S, P> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        // Verus requires us to pass mutable permission but
        // this is non-trivial in this case; the lock ensures
        // that the write is safe.
        self.lock.lock.0.store(Tracked::assume_new(), false);
        self.lock.spin.lock_epilogue();
    }
}

impl<'a, T: WellFormed, S: Spin, P: SpinPermission<'a, T>> SpinLockGuard<'a, T, S, P> {
    /// Borrows the underlying data with the given permission.
    #[inline(always)]
    pub fn borrow(&'a self) -> (r: &'a T)
        requires
            self.wf(),
        ensures
            r == self.lock.data.into_inner_spec(),
    {
        vstd::vpanic!("todo")
    }
}

/// A spinlock that provides mutual exclusion along with runtime permission tracking.
///
/// This spinlock allows threads to acquire exclusive access to the protected data
/// while dynamically managing access permissions. It creates temporary read/write
/// permissions for the duration of the lock hold like below:
///
/// ```rust,
///     impl SpinLockPermission<MyData> for vstd::simple_pptr:PointsTo<MyData> {
///     fn create() -> Self {
///
///     }
///
///     let lock: SpinLock<MyData, MyPermission> = SpinLock::new(MyData::new());
/// ```
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(P)]
pub struct SpinLock<T: ?Sized, S: Spin, P> {
    /// The unique id for this lock.
    pub id: Ghost<int>,
    /// The atomic boolean indicating the lock state.
    pub lock: (PAtomicBool, Tracked<PermissionBool>),
    /// The spin strategy.
    pub spin: S,
    pub __marker: core::marker::PhantomData<P>,
    /// The protected data; unfortunately [`vstd::cell::PCell`] is not
    /// `?Sized` so we cannot use it here.
    pub data: SpinCell<T>,
}

impl<'a, T: ?Sized, S: Spin, P> !Clone for SpinLockGuard<'a, T, S, P> {

}

impl<'a, T: ?Sized, S: Spin, P> !Copy for SpinLockGuard<'a, T, S, P> {

}

impl<T, S: Spin, P> SpinLock<T, S, P> {
    /// Creates a new [`SpinMutex`] wrapping the supplied data.
    ///
    /// # Example
    ///
    /// ```rust,norun
    /// verus! {
    ///     pub static MY_SPINLOCK: SpinLock<u32, SpinNoIrq> = SpinLock::new(0);
    ///
    ///     fn increment_spinlock() {
    ///        let (guard, Tracked(perm)) = MY_SPINLOCK.lock();
    ///        let value = *guard.borrow(Tracked(&perm)); // ✅ Access the data safely
    ///    }
    /// } // verus!
    /// ```
    #[inline(always)]
    pub const fn new(data: T, spin: S) -> Self {
        SpinLock {
            lock: PAtomicBool::new(false),
            spin,
            data: SpinCell::new(data),
            __marker: core::marker::PhantomData,
            id: Ghost(arbitrary()),
        }
    }
}

impl<T: Sized + WellFormed, S: Spin, P> SpinLock<T, S, P> {
    /// Consumes this lock and returns the underlying data.
    #[inline(always)]
    pub fn into_inner(self) -> (r: T)
        requires
            self.wf(),
        ensures
            r == self.data.into_inner_spec(),
    {
        self.data.into_inner()
    }
}

impl<'a, T: ?Sized + WellFormed, S: Spin, P: SpinPermission<'a, T>> SpinLock<T, S, P> {
    #[inline(always)]
    #[verifier::external_body]
    fn try_mark_locked(&self) -> Result<bool, bool> {
        self.lock.0.compare_exchange(Tracked::assume_new(), false, true)
    }

    /// Tries to acquire the spinlock.
    #[verifier::exec_allows_no_decreases_clause]
    fn try_get_lock(&self) -> bool
        requires
            self.wf(),
    {
        while self.try_mark_locked().is_err_and(|e| e == true)
            invariant
                self.wf(),
        {
            // Check if we can acquire the lock.
            let mut loop_count = 0usize;
            while self.lock.0.load(Tracked(self.lock.1.borrow()))
                invariant
                    0 <= loop_count <= MAX_ATTEMPT,
                    self.wf(),
                decreases MAX_ATTEMPT - loop_count,
            {
                core::hint::spin_loop();

                loop_count += 1;
                if loop_count >= MAX_ATTEMPT {
                    return false;
                }
            }
        }

        true
    }

    /// Locks the spinlock, blocking the current thread until it is able to do so.
    ///
    /// This function returns a [`SpinLockGuard`] that contains the corresponding
    /// permission model for accessing the protected data.
    #[inline(always)]
    pub fn lock(&self) -> (r: SpinLockGuard<'_, T, S, P>)
        requires
            self.wf(),
        ensures
            r.lock == self,
    {
        if self.try_get_lock() {
            let guard_data = S::lock_prologue();

            SpinLockGuard {
                id: self.id,
                lock: self,
                data: guard_data,
                perm: Tracked(P::create_new(&self.data.into_inner_spec())),
            }
        } else {
            // Perhaps we are having contention?
            vstd::vpanic!("Failed to acquire spinlock after maximum attempts");
        }
    }
}

impl<T: ?Sized + WellFormed, S: Spin, P> WellFormed for SpinLock<T, S, P> {
    open spec fn wf(&self) -> bool {
        &&& self.lock.0.id() == self.lock.1@@.patomic
    }
}

} // verus!
