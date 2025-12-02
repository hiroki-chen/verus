//! Mutex implementation in Verus.
//!
//! TODO: This is incomplete as we do not yet have anything to reason about the
//!       "wf" predicate on the cell.
//!
//! I'm not sure whether we stick to using `Mutex` or switch to `RwLock` as Verus
//! standard library already has a working `RwLock` implementation.
use vstd::atomic::{AtomicCellId, PAtomicBool, PermissionBool};
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::modes::*;
use vstd::open_atomic_invariant;
use vstd::prelude::*;
use vstd::simple_pptr::MemContents;

use crate::prelude::*;

verus! {

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
    // todo: replace it with 'invcell`?
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
            points_to@.id() == self.cell.id(),
            points_to@.mem_contents() matches MemContents::Init(value)
                && self.inv@.constant().2@.inv(value),
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

    pub fn release(&self, Tracked(points_to): Tracked<PointsTo<V>>)
        requires
            self.wf(),
            points_to.id() == self.cell.id(),
            points_to.mem_contents() matches MemContents::Init(value)
                && self.inv@.constant().2@.inv(value),
    {
        open_atomic_invariant!(self.inv.borrow() => perms => {
            let tracked (mut atomic_permission, _) = perms;
            self.atomic.store(Tracked(&mut atomic_permission), false);
            proof {
                perms = (atomic_permission, Some(points_to));
            }
        });
    }
}

} // verus!
