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

// ANCHOR: fields
tokenized_state_machine!(Rc<V: WellFormed> {
    fields {
        #[sharding(variable)]
        pub counter: nat,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| #[trigger] self.reader.count(t) > 0 ==> self.storage == Some(t) && t.wf()
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.counter == 0 ==> self.storage is None
    }

    #[invariant]
    pub fn counter_agrees_storage_rev(&self) -> bool {
        self.storage is None ==> self.counter == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage matches Some(v) ==>
            self.reader.count(self.storage->0) == self.counter && v.wf()
    }

    init!{
        initialize_empty() {
            init counter = 0;
            init storage = Option::None;
            init reader = Multiset::empty();
            // init inv = core::marker::PhantomData;
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self) { }

    transition! {
        do_deposit(x: V) {
            require(pre.counter == 0);
            require(x.wf());
            update counter = 1;
            deposit storage += Some(x);
            add reader += {x};
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, x: V) {
        assert(x.wf());
    }

    property! {
        reader_guard(x: V) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    transition! {
        do_clone(x: V) {
            have reader >= {x};
            add reader += {x};
            update counter = pre.counter + 1;
        }
    }

    #[inductive(do_clone)]
    fn do_clone_inductive(pre: Self, post: Self, x: V) {
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
        assert(pre.storage is Some);
        assert(pre.counter > 0);
    }

    transition! {
        dec_basic(x: V) {
            require(pre.counter >= 2);
            remove reader -= {x};
            update counter = (pre.counter - 1) as nat;
        }
    }

    transition! {
        dec_to_zero(x: V) {
            remove reader -= {x};
            require(pre.counter < 2);
            assert(pre.counter == 1);
            update counter = 0;
            withdraw storage -= Some(x);
        }
    }

    #[inductive(dec_basic)]
    fn dec_basic_inductive(pre: Self, post: Self, x: V) {
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
    }

    #[inductive(dec_to_zero)]
    fn dec_to_zero_inductive(pre: Self, post: Self, x: V) { }
});

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
    /// The strong counter.
    pub count: PAtomicU64,
    /// The actual data.
    pub data: V,
}

impl<V> ArcInner<V> {
    pub open spec fn wf(&self, cell: PAtomicU64) -> bool {
        self.count == cell
    }
}

#[verifier::reject_recursive_types(V)]
pub tracked struct ArcStatus<V> {
    pub count: PermissionU64,
    /// A state machine to track the state of the `Arc`.
    /// This allows us to reason about the reference counter.
    pub data: Rc::counter<DekoPointsTo<ArcInner<V>>>,
    // pub f: Ghost<F>,
}

impl<V> ArcStatus<V> {
    pub open spec fn wf(
        &self,
        inst: Rc::Instance<DekoPointsTo<ArcInner<V>>>,
        cell: PAtomicU64,
    ) -> bool {
        &&& self.count@.patomic == cell.id()
        &&& self.data.instance_id() == inst.id()
        &&& self.count@.value as nat
            == self.data.value()
        &&& 0 < self.count@.value < u64::MAX
        // &&& self.f@.inv(inst.value().data)
    }
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
///
/// This type also accepts an invariant `F` for the inner value `V`so that we are able to
/// reason about what is preserved during the reference counting operations. For more information
/// on invariants, see the [`Predicate`] trait.
///
/// FIXME: This is still a WIP;
#[verifier::reject_recursive_types(V)]
pub struct Arc<V> {
    /// The atomic holder of the `Arc` which contains the reference count and the inner value.
    ptr: DekoPPtr<ArcInner<V>>,
    /// The invariant that should be kept for the inner value.
    inv: Tracked<Shared<AtomicInvariant<_, ArcStatus<V>, _>>>,

    // state machines.
    inst: Tracked<Rc::Instance<DekoPointsTo<ArcInner<V>>>>,
    reader: Tracked<Rc::reader<DekoPointsTo<ArcInner<V>>>>,
    cell: Ghost<PAtomicU64>,
}

pub closed spec fn wf(&self) -> bool {
    predicate {
        &&& self.reader@.element().pptr() == self.ptr@
        &&& self.reader@.element().is_init()
        &&& self.reader@.element().value().count == self.cell
        &&& self.reader@.instance_id() == self.inst@.id()
        &&& self.reader@.element().wf()
    }

    invariant on inv with (inst, cell) specifically (self.inv@@) is (value: ArcStatus<V>) {
        value.wf(inst@, cell@)
    }
}
}

impl<U> View for Arc<U> {
    type V = U;

    closed spec fn view(&self) -> Self::V {
        self.reader@.element().value().data
    }
}

impl<V> Arc<V> {
    /// Constructs a new `Arc<T>` with the given value and invariant.
    pub fn new<A: WellFormed + Heap>(v: V, allocator: &DekoHeapAllocator<A>) -> (s: Self)
        requires
            allocator.wf(),
        ensures
            s.wf(),
            s@ == v,
    {
        let (counter, Tracked(counter_perm)) = PAtomicU64::new(1);
        let arc_inner = ArcInner { count: counter, data: v };
        let (pptr, Tracked(points_to)) = DekoPPtr::new(arc_inner, allocator);

        let tracked (Tracked(inst), Tracked(mut token), _) = Rc::Instance::initialize_empty(None);
        let tracked reader = inst.do_deposit(points_to, &mut token, points_to);
        let tracked status = ArcStatus { count: counter_perm, data: token };

        let tr_inst = Tracked(inst);
        let tr_counter = Ghost(counter);
        let tracked inv = AtomicInvariant::new((tr_inst, tr_counter), status, ARC_ID);
        let tracked inv = Shared::new(inv);

        Arc {
            ptr: pptr,
            inv: Tracked(inv),
            inst: Tracked(inst),
            reader: Tracked(reader),
            cell: Ghost(counter),
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn clone(&self) -> (s: Self)
        requires
            self.wf(),
        ensures
            s.wf(),
            s@ == self@,
    {
        loop
            invariant
                self.wf(),
        {
            let tracked inst = self.inst.borrow();
            let tracked reader = self.reader.borrow();
            let tracked perm = inst.reader_guard(reader.element(), &reader);

            let inner_ref = self.ptr.borrow(Tracked(perm));

            let count;
            open_atomic_invariant! {
                self.inv.borrow().borrow() => g => {
                    let tracked ArcStatus {
                        count: mut atomic_count,
                        data: mut token,
                    } = g;

                    count = inner_ref.count.load(Tracked(&mut atomic_count));

                    proof {
                        g = ArcStatus { count: atomic_count, data: token };
                    }
                }
            };

            // Ensure that the reference count is valid.
            assume(count < u64::MAX - 1);

            let tracked mut new_reader = None;
            let res;
            open_atomic_invariant! {
                self.inv.borrow().borrow() => g => {
                    let tracked ArcStatus {
                        count: mut atomic_count,
                        data: mut token,
                    } = g;

                    res = inner_ref.count.compare_exchange_weak(
                        Tracked(&mut atomic_count),
                        count,
                        count + 1,
                    );

                    proof {
                        if res.is_ok() {
                            new_reader = Some(self.inst.borrow().do_clone(
                                reader.element(),
                                &mut token,
                                &reader));
                        }
                    }

                    proof {
                        g = ArcStatus { count: atomic_count, data: token };
                    }
                }
            };

            if res.is_ok() {
                return Arc {
                    ptr: self.ptr, // ptr is Copy
                    inv: Tracked(self.inv.borrow().clone()),
                    inst: self.inst.clone(),
                    reader: Tracked(new_reader.tracked_unwrap()),
                    cell: Ghost(self.cell@),
                };
            }
        }
    }
}
} // verus!
pub use vstd::rwlock::RwLock;

use crate::Predicate;
