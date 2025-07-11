//! This crate implements several important synchronization primitives:
//!
//! - `Mutex`: A mutual exclusion lock that can be used to protect shared data.
//! - `RwLock`: A read-write lock that allows multiple readers or a single writer.
//! - `POnceCell`: A synchronization primitive that allows a piece of code to be executed only once.
use builtin_macros::*;
use state_machines_macros::*;
use vstd::atomic::{AtomicCellId, PAtomicBool, PermissionBool};
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::simple_pptr::MemContents;
use vstd::*;

verus! {

pub spec const ATOMIC_CELL_ID: int = 0x114514;

pub struct MutexInv;

impl<V> InvariantPredicate<
    (AtomicCellId, CellId),
    (PermissionBool, Option<PointsTo<V>>),
> for MutexInv {
    open spec fn inv(
        cell_ids: (AtomicCellId, CellId),
        perms: (PermissionBool, Option<PointsTo<V>>),
    ) -> bool {
        // Ensures that the atomic cell id matches the cell id
        cell_ids.0 == perms.0.id() && match perms.1 {
            // Lock is taken
            None => perms.0.value() == true,
            // Lock is not taken
            Some(points_to) => points_to.id() == cell_ids.1 && points_to.is_init()
                && !perms.0.value(),
        }
    }
}

#[verifier::reject_recursive_types(V)]
pub struct Mutex<V> {
    pub atomic: PAtomicBool,
    pub cell: PCell<V>,
    pub inv: Tracked<
        AtomicInvariant<(AtomicCellId, CellId), (PermissionBool, Option<PointsTo<V>>), MutexInv>,
    >,
}

impl<V> Mutex<V> {
    pub closed spec fn wf(&self) -> bool {
        self.inv@.constant() == (self.atomic.id(), self.cell.id())
    }

    pub const fn new(value: V) -> (result: Self)
        ensures
            result.wf(),
    {
        let (atomic, Tracked(atomic_perm)) = PAtomicBool::new(false);
        let (cell, Tracked(cell_perm)) = PCell::new(value);
        let tracked inv = AtomicInvariant::new(
            (atomic.id(), cell.id()),
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
pub struct POnceCell<V: 'static> {
    pub cell: PCell<Option<V>>,
    pub state: vstd::atomic_ghost::AtomicU64<_, OnceCellState<V>, _>,
}

pub closed spec fn wf(&self) -> bool {
    invariant on state with (cell) is (v: u64, g: OnceCellState<V>) {
        match g {
            OnceCellState::Uninit(points_to) => {
                v == 0
                    && points_to.id() == cell.id()
                    && points_to.mem_contents() === MemContents::Init(None)
            }
            OnceCellState::Occupied => {
                v == 1
            }
            OnceCellState::Init(points_to) => {
                v == 2
                    && points_to.id() == cell.id()
                    && matches!(points_to.mem_contents(), MemContents::Init(Some(_)))
            }
        }
    }
}
}

/// A `POonceCell` is a permissioned version of `OnceCell` that can be used in
/// multi-threaded contexts; it is safe to declare these traits so long as
/// `self.wf()` holds.
#[verifier::external]
unsafe impl<V> Send for POnceCell<V> {}
#[verifier::external]
unsafe impl<V> Sync for POnceCell<V> {}

impl<V> POnceCell<V> {
    /// Constructs a new `POonceCell` in the uninitialized state.
    pub const fn new() -> (result: Self)
        ensures
            result.wf(),
    {
        let (cell, Tracked(points_to)) = PCell::new(None);
        let state = vstd::atomic_ghost::AtomicU64::new(
            Ghost(cell),
            0,
            Tracked(OnceCellState::Uninit(points_to)),
        );

        Self { cell, state }
    }

    pub fn init(&self, value: V)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        let cur_state =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {}
        };

        if cur_state != 0 {
            return ;
        } else {
            let tracked mut points_to = None;
            let res =
                atomic_with_ghost! {
                &self.state => compare_exchange(0, 1);
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
                self.cell.replace(Tracked(&mut points_to), Some(value));
                let tracked static_points_to = tracked_static_ref(points_to);
                atomic_with_ghost! {
                    &self.state => store(2); ghost g => {
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
        let res = atomic_with_ghost! {
            &self.state => load(); ghost g => {
                match g {
                    OnceCellState::Init(points_to_opt) => {
                        points_to = Some(points_to_opt);
                    }
                    _ => {}
                }
            }
        };

        if res == 2 {
            let tracked points_to = points_to.tracked_unwrap();
            let tracked static_points_to = tracked_static_ref(points_to);

            self.cell.borrow(Tracked(static_points_to)).as_ref()
        } else {
            None
        }
    }
}

} // verus!
