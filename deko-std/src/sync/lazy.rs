use vstd::atomic::AtomicCellId;
use vstd::atomic_ghost::atomic_with_ghost;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::invariant::AtomicInvariant;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::simple_pptr::MemContents;

use crate::prelude::*;

verus! {

pub tracked enum LazyCellState<V: 'static> {
    Uninit(PointsTo<Option<V>>),
    Occupied,
    Init(&'static PointsTo<Option<V>>),
}

/// A trait for lazily initialized values.
pub trait InitLazy: WellFormed + Sized {
    fn init_lazy<F: Predicate<Self>>(Ghost(f): Ghost<F>) -> (s: Self)
        ensures
            f.inv(s),
    ;
}

/// A lazily initialized value that is initialized on the first access.
pub type LazyLock<V, F> = LazyCell<V, F>;

struct_with_invariants! {
/// A value which is initialized on the first access.
///
/// This type is inherently thread-safe and can be used in statics.
#[verifier::reject_recursive_types(V)]
pub struct LazyCell<V, F> where V: WellFormed + 'static, F: Predicate<V> {
    cell: (PCell<Option<V>>, Ghost<F>),
    state: vstd::atomic_ghost::AtomicU64<_, LazyCellState<V>, _>,
}

pub closed spec fn wf(&self) -> bool {
    invariant on state with (cell) is (v: u64, state: LazyCellState<V>) {
        match state {
            LazyCellState::Uninit(points_to) => {
                &&& v == UNINIT
                &&& points_to.id() == cell.0.id()
                &&& points_to.mem_contents() matches MemContents::Init(None)
            }
            LazyCellState::Occupied => {
                &&& v == OCCUPIED
            }
            LazyCellState::Init(points_to) => {
                &&& v == INITED
                &&& points_to.id() == cell.0.id()
                &&& points_to.mem_contents() matches MemContents::Init(Some(value))
                &&& cell.1@.inv(value)
            }
        }
    }
}
}

impl<V: WellFormed + InitLazy + 'static, F: Predicate<V>> LazyCell<V, F> {
    /// Constructs a new `LazyCell` in the uninitialized state.
    pub const fn new(Ghost(f): Ghost<F>) -> (s: Self)
        ensures
            s.wf(),
    {
        let (cell, Tracked(points_to)) = PCell::new(None);
        let tracked state = LazyCellState::Uninit(points_to);
        let state = vstd::atomic_ghost::AtomicU64::new(Ghost((cell, Ghost(f))), 0, Tracked(state));
        LazyCell { cell: (cell, Ghost(f)), state }
    }

    /// Gets the value from the cell, initializing it if necessary.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn get<'a>(&'a self) -> (s: &'a V)
        requires
            self.wf(),
        ensures
            self.inv(*s),
    {
        loop
            invariant
                self.wf(),
        {
            // We first check the state of the cell.
            let tracked mut reader: Option<&'static PointsTo<Option<V>>> = None;
            let state =
                atomic_with_ghost! {
                    &self.state => load(); ghost g => {
                        match &g {
                            LazyCellState::Init(points_to) => {
                                reader = Some(points_to);
                            }
                            _ => {}, // This should not happen.
                        }
                    }
                };

            if state == INITED {
                // Get the reference and return it.
                return self.cell.0.borrow(Tracked(reader.tracked_borrow())).as_ref().unwrap();
            }
            let tracked mut reader = None;
            if state == UNINIT {
                let res =
                    atomic_with_ghost! {
                        &self.state => compare_exchange(UNINIT, OCCUPIED); ghost g => {
                            g = match g {
                                LazyCellState::Uninit(points_to) => {
                                    reader = Some(points_to);
                                    LazyCellState::Occupied
                                }
                                _ => g,
                            }
                        }
                    };

                if res.is_err() {
                    continue ;
                }
            } else {
                continue ;
            }

            // Do the initialization.
            let v = V::init_lazy(self.cell.1);
            let tracked mut points_to = reader.tracked_unwrap();
            self.cell.0.replace(Tracked(&mut points_to), Some(v));
            let tracked static_points_to = tracked_static_ref(points_to);

            // Reaplce the status.
            atomic_with_ghost! {
                &self.state => store(INITED); ghost g => {
                    g = LazyCellState::Init(static_points_to);
                }
            };

            return self.cell.0.borrow(Tracked(static_points_to)).as_ref().unwrap();
        }
    }

    pub closed spec fn inv(&self, v: V) -> bool {
        self.cell.1@.inv(v)
    }
}

} // verus!
