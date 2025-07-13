//! This crate implements several important synchronization primitives:
//!
//! - `Mutex`: A mutual exclusion lock that can be used to protect shared data.
//! - `RwLock`: A read-write lock that allows multiple readers or a single writer <- exported from vstd.
//! - `POnceCell`: A synchronization primitive that allows a piece of code to be executed only once.
use builtin_macros::*;
use state_machines_macros::*;
use vstd::atomic::{AtomicCellId, PAtomicBool, PermissionBool};
#[cfg(feature = "alloc")]
use vstd::atomic::{PAtomicU64, PermissionU64};
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::shared::Shared;
use vstd::simple_pptr::MemContents;
#[cfg(feature = "alloc")]
use vstd::simple_pptr::PPtr;
use vstd::*;

verus! {

pub spec const ATOMIC_CELL_ID: int = 0x114514;

pub spec const ARC_ID: int = 0x1919810;

pub const UNINIT: u64 = 0;

pub const OCCUPIED: u64 = 1;

pub const INITED: u64 = 2;

pub struct MutexInv;

impl<V, F: Predicate<V>> InvariantPredicate<
    (AtomicCellId, CellId, Ghost<F>),
    (PermissionBool, Option<PointsTo<V>>),
> for MutexInv {
    open spec fn inv(
        cell_ids: (AtomicCellId, CellId, Ghost<F>),
        perms: (PermissionBool, Option<PointsTo<V>>),
    ) -> bool {
        // Ensures that the atomic cell id matches the cell id
        cell_ids.0 == perms.0.id() && match perms.1 {
            // Lock is taken
            None => perms.0.value() == true,
            // Lock is not taken
            Some(points_to) => {
                &&& points_to.id() == cell_ids.1
                &&& !perms.0.value()
                &&& points_to.mem_contents() matches MemContents::Init(value)
                &&& cell_ids.2@.inv(value)
            },
        }
    }
}

/// A spin-based lock providing mutually exclusive access to data.
///
/// The implementation uses either a ticket mutex or a regular spin-based primitive.
#[verifier::reject_recursive_types(V)]
pub struct Mutex<V, F: Predicate<V>> {
    pub atomic: PAtomicBool,
    pub cell: PCell<V>,
    pub inv: Tracked<
        AtomicInvariant<
            (AtomicCellId, CellId, Ghost<F>),
            (PermissionBool, Option<PointsTo<V>>),
            MutexInv,
        >,
    >,
}

impl<V, F: Predicate<V>> Mutex<V, F> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.inv@.constant().0 == self.atomic.id()
        &&& self.inv@.constant().1 == self.cell.id()
    }

    pub const fn new(value: V, Ghost(f): Ghost<F>) -> (result: Self)
        requires
            f.inv(value),
        ensures
            result.wf(),
    {
        let (atomic, Tracked(atomic_perm)) = PAtomicBool::new(false);
        let (cell, Tracked(cell_perm)) = PCell::new(value);
        let tracked inv = AtomicInvariant::new(
            (atomic.id(), cell.id(), Ghost(f)),
            (atomic_perm, Some(cell_perm)),
            ATOMIC_CELL_ID,
        );

        Self { atomic, cell, inv: Tracked(inv) }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (points_to: Tracked<PointsTo<V>>)
        requires
            self.wf(),
        ensures
            points_to@.id() == self.cell.id() && points_to@.is_init(),
    {
        loop
            invariant
                self.wf(),
        {
            let tracked points_to_opt = None;
            let res;

            open_atomic_invariant! {
                self.inv.borrow() => perms => {
                    let tracked (mut atomic_permission, mut points_to_inv) = perms;
                    res = self.atomic.compare_exchange(Tracked(&mut atomic_permission), false, true);
                    proof {
                        tracked_swap(&mut points_to_opt, &mut points_to_inv);
                        perms = (atomic_permission, points_to_inv);
                    }
                }
            }

            if res.is_ok() {
                return Tracked(points_to_opt.tracked_unwrap());
            }
        }

    }

    pub fn release(&self, points_to: Tracked<cell::PointsTo<V>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(),
            points_to@.is_init(),
            points_to@.mem_contents() matches MemContents::Init(value)
                && self.inv@.constant().2@.inv(value),
    {
        open_atomic_invariant!(self.inv.borrow() => perms => {
            let tracked (mut atomic_permission, _) = perms;
            self.atomic.store(Tracked(&mut atomic_permission), false);
            proof {
                perms = (atomic_permission, Some(points_to.get()));
            }
        });
    }
}

} // verus!
verus! {

/// A tracked state of a `OnceCell` that can be used to ensure that the cell is
/// initialized before accessing its value.
pub tracked enum OnceCellState<V: 'static> {
    /// The cell is uninitialized.
    Uninit(PointsTo<Option<V>>),
    /// The cell is occupied meaning it is being *written*.
    Occupied,
    /// The cell is initialized with a value.
    Init(&'static PointsTo<Option<V>>),
}

struct_with_invariants! {
/// A synchronization primitive which can nominally be written to only once.
///
/// This type is a thread-safe [`OnceCell`], and can be used in statics.
/// In many simple cases, you can use [`LazyLock<T, F>`] instead to get the benefits of this type
/// with less effort: `LazyLock<T, F>` "looks like" `&T` because it initializes with `F` on deref!
/// Where OnceLock shines is when LazyLock is too simple to support a given case, as LazyLock
/// doesn't allow additional inputs to its function after you call [`LazyLock::new(|| ...)`].
///
/// A `OnceLock` can be thought of as a safe abstraction over uninitialized data that becomes
/// initialized once written.
///
/// # Examples
///
/// ```rust
/// static MY_ONCE: POnceCell<i32> = POnceCell::new();
///
/// let value = MY_ONCE.get();
/// assert(value.is_some());   // unsatisfied precondition, as MY_ONCE is uninitialized.
/// ```
#[verifier::reject_recursive_types(V)]
pub struct POnceCell<V: 'static, F: Predicate<V>> {
    pub cell: (Ghost<F>, PCell<Option<V>>),
    pub state: vstd::atomic_ghost::AtomicU64<_, OnceCellState<V>, _>,
}

pub closed spec fn wf(&self) -> bool {
    invariant on state with (cell) is (v: u64, g: OnceCellState<V>) {
        match g {
            OnceCellState::Uninit(points_to) => {
                &&& v == UNINIT
                &&& points_to.id() == cell.1.id()
                &&& points_to.mem_contents() matches MemContents::Init(None)
            }
            OnceCellState::Occupied => {
                &&& v == OCCUPIED
            }
            OnceCellState::Init(points_to) => {
                &&& v == INITED
                &&& points_to.id() == cell.1.id()
                &&& points_to.mem_contents() matches MemContents::Init(Some(value))
                &&& cell.0@.inv(value)
            }
        }
    }
}
}

/// Export the `OnceCell` type as `OnceCell` for compatibility.
pub type OnceCell<V, F> = POnceCell<V, F>;

/// Export the `POonceCell` type as `OnceLock` for compatibility.
pub type OnceLock<V, F> = POnceCell<V, F>;

/// A `POonceCell` is a permissioned version of `OnceCell` that can be used in
/// multi-threaded contexts; it is safe to declare these traits so long as
/// `self.wf()` holds.
#[verifier::external]
unsafe impl<V, F: Predicate<V>> Send for POnceCell<V, F> {

}

#[verifier::external]
unsafe impl<V, F: Predicate<V>> Sync for POnceCell<V, F> {

}

impl<V, F: Predicate<V>> POnceCell<V, F> {
    pub closed spec fn inv(&self, v: V) -> bool {
        self.cell.0@.inv(v)
    }

    /// Constructs a new `POonceCell` in the uninitialized state.
    pub const fn new(Ghost(f): Ghost<F>) -> (result: Self)
        ensures
            result.wf(),
            result.cell.0@ === f,
    {
        let (cell, Tracked(points_to)) = PCell::new(None);
        let tracked state = OnceCellState::Uninit(points_to);
        let state = vstd::atomic_ghost::AtomicU64::new(
            Ghost((Ghost(f), cell)),
            UNINIT,
            Tracked(state),
        );

        Self { cell: (Ghost(f), cell), state }
    }

    pub fn init(&self, value: V)
        requires
            self.inv(value),
            self.wf(),
    {
        let cur_state =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {}
        };

        if cur_state != UNINIT {
            return ;
        } else {
            let tracked mut points_to = None;
            let res =
                atomic_with_ghost! {
                &self.state => compare_exchange(UNINIT, OCCUPIED);
                returning res; ghost g => {
                    g = match g {
                        OnceCellState::Uninit(points_to_inner) => {
                            points_to = Some(points_to_inner);
                            OnceCellState::Occupied
                        }
                        _ => {
                            // If we are not in Uninit state, we cannot do anything.
                            g
                        }
                    }
                }
            };

            if !res.is_err() {
                let tracked mut points_to = points_to.tracked_unwrap();
                self.cell.1.replace(Tracked(&mut points_to), Some(value));
                // Extending the permission to static because `OnceLock` is
                // often shared among threads and we want to ensure that
                // the value is accessible globally.
                let tracked static_points_to = tracked_static_ref(points_to);
                atomic_with_ghost! {
                    &self.state => store(INITED); ghost g => {
                        g = OnceCellState::Init(static_points_to);
                    }
                }
            } else {
                // wait or abort.
                return ;
            }
        }
    }

    pub fn get<'a>(&'a self) -> (result: Option<&'a V>)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        let tracked mut points_to = None;
        let res =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {
                match g {
                    OnceCellState::Init(points_to_opt) => {
                        points_to = Some(points_to_opt);
                    }
                    _ => {}
                }
            }
        };

        if res == INITED {
            let tracked points_to = points_to.tracked_unwrap();
            let tracked static_points_to = tracked_static_ref(points_to);

            self.cell.1.borrow(Tracked(static_points_to)).as_ref()
        } else {
            None
        }
    }
}

} // verus!
#[cfg(feature = "alloc")]
verus! {

use crate::boxed::Box;
use crate::prelude::*;

#[verifier::reject_recursive_types(V)]
pub struct ArcInner<V> {
    pub count: PAtomicU64,
    /// The actual data.
    pub data: V,
}

#[verifier::reject_recursive_types(V)]
pub tracked struct ArcStatus<V> {
    pub count: PermissionU64,
    pub data: vstd::simple_pptr::PointsTo<ArcInner<V>>,
}

struct_with_invariants! {
/// A thread-safe reference-counting pointer. 'Arc' stands for 'Atomically
/// Reference Counted'.
///
/// The type `Arc<T>` provides shared ownership of a value of type `T`,
/// allocated in the heap. Invoking [`clone`][clone] on `Arc` produces
/// a new `Arc` instance, which points to the same allocation on the heap as the
/// source `Arc`, while increasing a reference count. When the last `Arc`
/// pointer to a given allocation is destroyed, the value stored in that allocation (often
/// referred to as "inner value") is also dropped.
///
/// Shared references in Rust disallow mutation by default, and `Arc` is no
/// exception: you cannot generally obtain a mutable reference to something
/// inside an `Arc`. If you do need to mutate through an `Arc`, you have several options:
///
/// 1. Use interior mutability with synchronization primitives like [`Mutex`][mutex],
///    [`RwLock`][rwlock], or one of the [`Atomic`][atomic] types.
///
/// 2. Use clone-on-write semantics with [`Arc::make_mut`] which provides efficient mutation
///    without requiring interior mutability. This approach clones the data only when
///    needed (when there are multiple references) and can be more efficient when mutations
///    are infrequent.
///
/// 3. Use [`Arc::get_mut`] when you know your `Arc` is not shared (has a reference count of 1),
///    which provides direct mutable access to the inner value without any cloning.
#[verifier::reject_recursive_types(V)]
pub struct Arc<V> {
    /// The atomic holder of the `Arc` which contains the reference count and the inner value.
    pub ptr: PPtr<ArcInner<V>>,
    /// Tracks the state.
    pub state: vstd::atomic_ghost::AtomicU64<_, Shared<ArcStatus<V>>, _>,
}

pub closed spec fn wf(&self) -> bool {
    invariant on state with (ptr) is (count: u64, status: Shared<ArcStatus<V>>) {
        // No dangling pointer.
        &&& status@.data.is_init()
        // Ensure that we always have a valid pointer to the inner value.
        // Also this remains the same data for all clones.
        &&& ptr === status@.data.pptr()
        // Ensure that the reference count is valid.
        &&& count >= 0 &&& count == status@.count.value()
    }
}

}

impl<V: Sized> Arc<V> {
    #[verifier::external_body]
    pub const fn new<A: WellFormed + Heap>(value: V, allocator: &DekoAllocator<A>) -> (result: Self)
        requires
            allocator.wf(),
        ensures
            result.wf(),
    {
        // We will leak the memory created by a Box
        todo!()
        // let (count, Tracked(count_perm)) = PAtomicU64::new(1);
        // let (cell, Tracked(points_to)) = PCell::new(ArcInner {
        //     count,
        //     data: value,
        // });
        // let state = vstd::atomic_ghost::AtomicU64::new(
        //     Ghost(cell),
        //     1,
        //     Tracked(Shared::new(ArcStatus { count: count_perm, data: points_to })),
        // );
        // Self { ptr, state }

    }
}

} // verus!
pub use vstd::rwlock::RwLock;

use crate::Predicate;
