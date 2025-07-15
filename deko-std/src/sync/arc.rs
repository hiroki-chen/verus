use state_machines_macros::*;
use vstd::atomic::{PAtomicU64, PermissionU64};
use vstd::invariant::AtomicInvariant;
use vstd::multiset::Multiset;
use vstd::open_atomic_invariant;
use vstd::prelude::*;
use vstd::shared::*;

use crate::prelude::*;

verus! {

// ANCHOR: fields
tokenized_state_machine!(
    Rc<V, F>
    where
        V: WellFormed,
        F: Predicate<V>,
    {
    fields {
        #[sharding(variable)]
        pub counter: nat,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(constant)]
        pub inv: F,

        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }
// ANCHOR_END: fields

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| #[trigger] self.reader.count(t) > 0 ==>
            self.storage == Some(t) && t.wf() && self.inv.inv(t)
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.counter == 0 <==> self.storage is None
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage matches Some(v) ==>
            self.reader.count(self.storage->0) == self.counter && v.wf() && self.inv.inv(v)
    }

    init! {
        initialize_empty(f: F) {
            init counter = 0;
            init storage = Option::None;
            init reader = Multiset::empty();
            init inv = f;
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self, f: F) { }

    transition! {
        do_deposit(x: V) {
            require(pre.counter == 0);
            require(pre.inv.inv(x));
            require(x.wf());
            update counter = 1;
            deposit storage += Some(x);
            add reader += {x};
        }
    }

    #[inductive(do_deposit)]
    fn do_deposit_inductive(pre: Self, post: Self, x: V) {
        assert(x.wf());
        assert(post.inv.inv(x));
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
            require(pre.inv.inv(x));
            remove reader -= {x};
            update counter = (pre.counter - 1) as nat;
        }
    }

    transition! {
        dec_to_zero(x: V) {
            remove reader -= {x};
            require(pre.counter < 2);
            require(pre.inv.inv(x));
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

} // verus!
verus! {

#[verifier::reject_recursive_types(V)]
pub struct ArcInner<V> {
    /// The strong counter.
    pub count: PAtomicU64,
    /// The actual data.
    pub data: V,
}

/// A wrapped predicate for the `Arc` type.
///
/// Why do we need this type? This is because we have to reason about the inner permissioned
/// types but for the user API we expose the predicate like `V -> bool` so we need a proxy
/// to convert `V -> bool` into `DekoPointsTo<ArcInner<V>> -> bool`. This ghost struct does
/// the conversion; also, since this is a ghost type, we can use it to reason about the
#[verifier::reject_recursive_types(V)]
pub ghost struct ArcPredicateWrapper<V, F> where V: WellFormed, F: Predicate<V> {
    v: V,
    f: F,
}

// Lift the predicate to the `DekoPointsTo<ArcInner<V>>` type.
impl<V, F> Predicate<DekoPointsTo<ArcInner<V>>> for ArcPredicateWrapper<V, F> where
    V: WellFormed,
    F: Predicate<V>,
 {
    closed spec fn inv(self, points_to: DekoPointsTo<ArcInner<V>>) -> bool {
        self.f.inv(points_to.value().data)
    }
}

#[verifier::reject_recursive_types(V)]
pub tracked struct ArcStatus<V, F> where V: WellFormed, F: Predicate<V> {
    pub count: PermissionU64,
    /// A state machine to track the state of the `Arc`.
    /// This allows us to reason about the reference counter.
    pub data: Rc::counter<
        DekoPointsTo<ArcInner<V>>,
        ArcPredicateWrapper<V, F>,
    >,
    // pub f: Ghost<F>,
}

impl<V, F> ArcStatus<V, F> where V: WellFormed, F: Predicate<V> {
    pub open spec fn wf(
        &self,
        inst: Rc::Instance<DekoPointsTo<ArcInner<V>>, ArcPredicateWrapper<V, F>>,
        cell: PAtomicU64,
    ) -> bool {
        &&& self.count@.patomic == cell.id()
        &&& self.data.instance_id() == inst.id()
        &&& self.count@.value as nat == self.data.value()
        &&& 0 < self.count@.value < u64::MAX
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
pub struct Arc<V, F>
where
    V: WellFormed,
    F: Predicate<V>,
{
    /// The atomic holder of the `Arc` which contains the reference count and the inner value.
    ptr: (DekoPPtr<ArcInner<V>>, Ghost<F>),
    /// The invariant that should be kept for the inner value.
    inv: Tracked<Shared<AtomicInvariant<_, ArcStatus<V, F>, _>>>,

    // state machines.
    inst: Tracked<Rc::Instance<DekoPointsTo<ArcInner<V>>, ArcPredicateWrapper<V, F>>>,
    reader: Tracked<Rc::reader<DekoPointsTo<ArcInner<V>>, ArcPredicateWrapper<V, F>>>,
    cell: Ghost<PAtomicU64>,
}

#[verifier::type_invariant]
pub closed spec fn wf(&self) -> bool {
    predicate {
        &&& self.reader@.element().pptr() == self.ptr.0@
        &&& self.reader@.element().is_init()
        &&& self.reader@.element().value().count == self.cell
        &&& self.reader@.instance_id() == self.inst@.id()
        &&& self.reader@.element().wf()
        &&& self.ptr.1@.inv(self@)
    }

    invariant on inv with (inst, cell) specifically (self.inv@@) is (value: ArcStatus<V, F>) {
        value.wf(inst@, cell@)
    }
}
}

impl<U, F> View for Arc<U, F> where U: WellFormed, F: Predicate<U> {
    type V = U;

    closed spec fn view(&self) -> Self::V {
        self.reader@.element().value().data
    }
}

impl<V, F> Arc<V, F> where V: WellFormed, F: Predicate<V> {
    pub closed spec fn inv(&self, v: V) -> bool {
        self.ptr.1@.inv(v)
    }

    pub closed spec fn f(&self) -> Ghost<F> {
        self.ptr.1
    }

    /// Constructs a new `Arc<T>` with the given value and invariant.
    pub fn new<A: WellFormed + Heap>(
        v: V,
        allocator: &DekoHeapAllocator<A>,
        Ghost(f): Ghost<F>,
    ) -> (s: Self)
        requires
            f.inv(v),
            allocator.wf(),
        ensures
            s.wf(),
            s@ == v,
            s.f() == f,
            s.inv(v),
    {
        let (counter, Tracked(counter_perm)) = PAtomicU64::new(1);
        let arc_inner = ArcInner { count: counter, data: v };
        let ghost wrapper = ArcPredicateWrapper { v, f };
        let (pptr, Tracked(points_to)) = DekoPPtr::new(arc_inner, allocator);

        let tracked (Tracked(inst), Tracked(mut token), _) = Rc::Instance::<
            DekoPointsTo<ArcInner<V>>,
            ArcPredicateWrapper<V, F>,
        >::initialize_empty(wrapper, None);
        let tracked reader = inst.do_deposit(points_to, &mut token, points_to);
        let tracked status = ArcStatus { count: counter_perm, data: token };

        let tr_inst = Tracked(inst);
        let tr_counter = Ghost(counter);
        let tracked inv = AtomicInvariant::new((tr_inst, tr_counter), status, ARC_ID);
        let tracked inv = Shared::new(inv);

        Arc {
            ptr: (pptr, Ghost(f)),
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

            let inner_ref = self.ptr.0.borrow(Tracked(perm));

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
                    ptr: self.ptr,  // ptr is Copy
                    inv: Tracked(self.inv.borrow().clone()),
                    inst: self.inst.clone(),
                    reader: Tracked(new_reader.tracked_unwrap()),
                    cell: Ghost(self.cell@),
                };
            }
        }
    }

    /// Converts this type into a shared reference of the (usually inferred) input type.
    pub fn as_ref<'a>(&'a self) -> (v: &'a V)
        requires
            self.wf(),
        ensures
            *v == self@,
    {
        let tracked inst = self.inst.borrow();
        let tracked reader = self.reader.borrow();
        let tracked perm = inst.reader_guard(reader.element(), &reader);

        &self.ptr.0.borrow(Tracked(perm)).data
    }

    /// Immutably borrows from an owned value.
    ///
    /// For [`Arc<V, F>`], this is equivalent to [`Arc::as_ref`].
    #[inline(always)]
    pub fn borrow<'a>(&'a self) -> (v: &'a V) {
        proof {
            use_type_invariant(&*self);
        }
        self.as_ref()
    }
}

} // verus!
