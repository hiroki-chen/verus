use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic::PAtomicBool;
use vstd::atomic_with_ghost;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::modes::*;
use vstd::prelude::*;
use vstd::simple_pptr::MemContents;

use crate::prelude::*;

verus! {

pub type DekoSimpleOnceCell<V> = OnceCell<V, ()>;

pub type DekoOnceCell<V, P, Pred> = OnceCell<DekoAtomicData<V, P>, Pred>;

/// A tracked state of a¸ `OnceCell` that can be used to ensure that the cell is
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
/// static MY_ONCE: OnceCell<i32> = OnceCell::new();
///
/// let value = MY_ONCE.get();
/// assert(value.is_some());   // unsatisfied precondition, as MY_ONCE is uninitialized.
/// ```
#[verifier::reject_recursive_types(V)]
pub struct OnceCell<V: 'static + WellFormed, F: Predicate<V>> {
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

/// Export the `POonceCell` type as `OnceLock` for compatibility.
pub type OnceLock<V, F> = OnceCell<V, F>;

/// A `POonceCell` is a permissioned version of `OnceCell` that can be used in
/// multi-threaded contexts; it is safe to declare these traits so long as
/// `self.wf()` holds.
#[verifier::external]
unsafe impl<V: WellFormed, F: Predicate<V>> Send for OnceCell<V, F> {

}

#[verifier::external]
unsafe impl<V: WellFormed, F: Predicate<V>> Sync for OnceCell<V, F> {

}

impl<V: WellFormed, F: Predicate<V>> OnceCell<V, F> {
    pub open spec fn inv(&self, v: V) -> bool {
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
                // let tracked _ = self.inst.borrow().do_deposit(points_to, points_to, &mut token);
                atomic_with_ghost! {
                    &self.state => store(INITED); ghost g => {
                        g = OnceCellState::Init(static_points_to);
                    }
                }
                return ;
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
            result matches Some(res) ==> self.inv(*res),
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

impl<V: 'static + WellFormed + DekoDebug, F: Predicate<V>> DekoDebug for OnceCell<V, F> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str("OnceCell(...)");
    }
}

} // verus!
