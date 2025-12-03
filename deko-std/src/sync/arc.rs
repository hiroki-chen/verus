use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic::{PAtomicU64, PAtomicUsize, PermissionU64, PermissionUsize};
use vstd::invariant::{self, AtomicInvariant};
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::shared::Shared;
use vstd::{atomic_with_ghost, open_atomic_invariant};

use crate::ptr::{DekoPPtr, DekoPointsTo};
use crate::wf::WellFormed;
use crate::{boxed_ptr, DefaultDekoHeapAllocator, Predicate, ARC_ID};

verus! {

tokenized_state_machine! {
    Rc<V: WellFormed, RcPerm, F: Predicate<V>> {
        fields {
            #[sharding(storage_option)]
            pub storage: Option<RcPerm>,

            #[sharding(storage_option)]
            pub data: Option<Ghost<V>>,

            #[sharding(variable)]
            pub count: nat,

            #[sharding(constant)]
            pub f: F,

            /// The multiset of readers.
            #[sharding(multiset)]
            pub reader: Multiset<RcPerm>,
    }

    #[invariant]
    pub fn data_always_wf(&self) -> bool {
        self.data matches Some(v) ==> v@.wf() && self.f.inv(v@)
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |p: RcPerm| #[trigger] self.reader.count(p) > 0 ==> self.storage == Some(p)
    }

    #[invariant]
    pub fn storage_agrees_data(&self) -> bool {
        self.storage is Some <==> self.data is Some
    }

    #[invariant]
    pub fn count_agrees_storage(&self) -> bool {
        self.storage is None <==> self.count == 0
    }

    #[invariant]
    pub fn counter_agrees_reader_count(&self) -> bool {
        self.storage is Some ==> self.reader.count((self.storage->0)) == self.count
    }

    init! {
        initialize_empty(f: F) {
            init count = 0;
            init storage = None;
            init data = None;
            init reader = Multiset::empty();
            init f = f;
        }
    }

    #[inductive(initialize_empty)]
    pub fn initialize_empty_inductive(post: Self, f: F) { }

    transition! {
        do_deposit(v: Ghost<V>, p: RcPerm) {
            require(pre.count == 0);
            require(pre.f.inv(v@));
            require(v@.wf());

            update count = 1;
            deposit data += Some(v);
            deposit storage += Some(p);
            add reader += {p};
        }
    }

    #[inductive(do_deposit)]
    pub fn do_deposit_inductive(pre: Self, post: Self, v: Ghost<V>, p: RcPerm) {
        assert(post.reader.count(p) == 1);
        assert(post.storage == Some(p));
        assert(post.data == Some(v));
        assert(post.count == 1);
    }

    property! {
        reader_guard(p: RcPerm) {
            have reader >= {p};
            guard storage >= Some(p);
        }
    }

    transition! {
        do_clone(p: RcPerm) {
            have reader >= {p};
            add reader += {p};
            update count = pre.count + 1;
        }
    }

    #[inductive(do_clone)]
    pub fn do_clone_inductive(pre: Self, post: Self, p: RcPerm) {
        assert(pre.reader.count(p) > 0);
        assert(pre.storage == Some(p));
        assert(pre.storage is Some);
        assert(pre.count > 0);
    }

    transition! {
        dec(p: RcPerm) {
            require(pre.count >= 2);

            remove reader -= {p};
            update count = (pre.count - 1) as nat;
        }
    }

    #[inductive(dec)]
    pub fn dec_inductive(pre: Self, post: Self, p: RcPerm) {
        assert(pre.reader.count(p) >= 2);
        assert(pre.storage == Some(p));
        assert(pre.data == post.data);
        assert(post.count >= 1);
    }

    transition! {
        do_free(p: RcPerm) {
            require(pre.count == 1);

            remove reader -= {p};
            update count = 0;

            birds_eye let v = pre.data->0;
            withdraw storage -= Some(p);
            withdraw data -= Some(v);
        }
    }

    #[inductive(do_free)]
    pub fn do_free_inductive(pre: Self, post: Self, p: RcPerm) {
        assert(pre.reader.count(p) == 1);
        assert(pre.storage == Some(p));
        assert(post.count == 0);
    }
}
}  // tokenized_state_machine!


pub struct ArcInner<V: WellFormed> {
    count: PAtomicUsize,
    data: DekoPPtr<V>,
}

impl<V: WellFormed> WellFormed for ArcInner<V> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

#[verifier::reject_recursive_types(V)]
pub tracked struct ArcStatus<V: WellFormed, F: Predicate<V>> {
    pub count: PermissionUsize,
    /// A state machine to track the state of the `DekoArc`.
    /// This allows us to reason about the reference counter.
    pub data: Rc::count<V, DekoPointsTo<ArcInner<V>>, F>,
    /// The "actual permission" to the data held by the `DekoArc`.
    pub data_perm: Option<DekoPointsTo<V>>,
}

impl<V: WellFormed, F: Predicate<V>> ArcStatus<V, F> {
    pub open spec fn wf_with(
        self,
        inst: Rc::Instance<V, DekoPointsTo<ArcInner<V>>, F>,
        data: V,
        data_ptr: DekoPPtr<V>,
        ref_count: PAtomicUsize,
    ) -> bool {
        &&& self.count@.patomic == ref_count.id()
        &&& self.data.instance_id() == inst.id()
        &&& self.count.value() as nat == self.data.value()
        &&& 0 <= self.count@.value < u64::MAX
        &&& self.count@.value == 0 <==> self.data_perm is None
        &&& self.count@.value > 0 <==> self.data_perm is Some
        &&& self.data_perm matches Some(data_perm) ==> {
            &&& data_perm.pptr() == data_ptr@
            &&& data_perm.value() == data
            &&& data_perm.is_init()
            &&& data_perm.wf()
        }
    }
}

struct_with_invariants! {

/// A thread-safe reference-counting pointer. 'DekoArc' stands for 'Atomically
/// Reference Counted'.
///
/// The type [`DekoArc<T>`] provides shared ownership of a value of type `T`,
/// allocated in the heap. Invoking [`clone`][clone] on `DekoArc` produces
/// a new `DekoArc` instance, which points to the same allocation on the heap as the
/// source `DekoArc`, while increasing a reference count. When the last `DekoArc`
/// pointer to a given allocation is destroyed, the value stored in that allocation (often
/// referred to as "inner value") is also dropped.
#[verifier::reject_recursive_types(V)]
pub struct DekoArc<V: WellFormed, F: Predicate<V>> {
    /// The shared pointer to the inner data.
    ptr: DekoPPtr<ArcInner<V>>,
    /// The invariant that should be kept for the inner value.
    inv: Tracked<Shared<AtomicInvariant<_, ArcStatus<V, F>, _>>>,
    // state machines.
    inst: Tracked<Rc::Instance<V, DekoPointsTo<ArcInner<V>>, F>>,
    reader: Tracked<Rc::reader<V, DekoPointsTo<ArcInner<V>>, F>>,

    data: Ghost<V>,
    data_ptr: Ghost<DekoPPtr<V>>,
    ref_count: Ghost<PAtomicUsize>,
}

#[verifier::type_invariant]
pub closed spec fn wf(&self) -> bool {
    predicate {
        &&& self.reader@.element().value().count == self.ref_count@
        &&& self.reader@.instance_id() == self.inst@.id()
        &&& self.reader@.element().pptr() == self.ptr@
        &&& self.reader@.element().is_init()
        &&& self.reader@.element().value().data == self.data_ptr
        &&& self.reader@.element().wf()
    }

    invariant on inv with (inst, data, data_ptr, ref_count) specifically (self.inv@@) is (value: ArcStatus<V, F>) {
        value.wf_with(inst@, data@, data_ptr@, ref_count@)
    }
}

}  // struct_with_invariants!


impl<U, F> View for DekoArc<U, F> where U: WellFormed, F: Predicate<U> {
    type V = U;

    closed spec fn view(&self) -> Self::V {
        self.data@
    }
}

impl<V: WellFormed, F: Predicate<V>> WellFormed for DekoArc<V, F> {
    closed spec fn wf(&self) -> bool {
        true
    }
}

impl<V: WellFormed, F: Predicate<V>> DekoArc<V, F> {
    pub closed spec fn inv(&self, v: V) -> bool {
        self.inst@.f().inv(v)
    }

    fn new_with_inner(
        data: DekoPPtr<V>,
        inner: DekoPPtr<ArcInner<V>>,
        v: V,
        Tracked(data_perm): Tracked<DekoPointsTo<V>>,
        Tracked(inner_perm): Tracked<DekoPointsTo<ArcInner<V>>>,
        Ghost(f): Ghost<F>,
    ) -> (r: Self)
        requires
            v.wf(),
            f.inv(v),
            data_perm.wf(),
            inner_perm.wf(),
            data@ == data_perm.pptr(),
            inner@ == inner_perm.pptr(),
        ensures
            r.wf(),
            r@ == v,
    {
        let tracked mut data_perm = data_perm;
        let tracked mut inner_perm = inner_perm;

        let (count, Tracked(mut count_perm)) = PAtomicUsize::new(1);
        inner.write(Tracked(&mut inner_perm), ArcInner { count, data });
        data.write(Tracked(&mut data_perm), v);

        let tracked (Tracked(inst), Tracked(mut token), _) = Rc::Instance::<
            V,
            DekoPointsTo<ArcInner<V>>,
            F,
        >::initialize_empty(f, None, None);

        let tracked reader = inst.do_deposit(
            Ghost(data_perm.value()),
            inner_perm,
            inner_perm,
            Ghost(data_perm.value()),
            &mut token,
        );
        let tracked status = ArcStatus {
            count: count_perm,
            data: token,
            data_perm: Some(data_perm),
        };
        let tr_inst = Tracked(inst);
        let ghost_ptr = Ghost(data);
        let ghost_data = Ghost(v);
        let ghost_count = Ghost(count);
        let tracked inv: AtomicInvariant<_, ArcStatus<_, _>, _> = AtomicInvariant::new(
            (tr_inst, ghost_data, ghost_ptr, ghost_count),
            status,
            ARC_ID,
        );
        let tracked inv = Shared::new(inv);

        Self {
            ptr: inner,
            inv: Tracked(inv),
            inst: Tracked(inst),
            reader: Tracked(reader),
            data: Ghost(v),
            data_ptr: Ghost(data),
            ref_count: Ghost(count),
        }
    }

    /// Constructs a new [`DekoArc<T>`] instance with the given value `v`, using the provided allocator
    /// and with a predicate `f` that should hold for the inner value.
    pub fn new(v: V, allocator: &DefaultDekoHeapAllocator, Ghost(f): Ghost<F>) -> (r: Self)
        requires
            allocator.wf(),
            v.wf(),
            f.inv(v),
        ensures
            r.wf(),
            r@ == v,
    {
        let v_g = Ghost(v);

        let (data, Tracked(mut data_perm)) = boxed_ptr!(V, allocator);
        let (inner, Tracked(mut inner_perm)) = boxed_ptr!(ArcInner<V>, allocator);

        Self::new_with_inner(data, inner, v, Tracked(data_perm), Tracked(inner_perm), Ghost(f))
    }

    /// Clone this [`DekoArc`] and increase the strong reference count.
    ///
    /// This operation is safe and will not create duplicate ownership to the
    /// inner value as we never expose any APIs to the outside world that can
    /// transfer or mutate ownership. The inner value is only accessible through
    /// shared references like [`Self::as_ref`] or [`Self::borrow`].
    ///
    /// Due to some limitations in the transition system, we do not (yet) allow
    /// mutating the [`DekoArc`] in a way as Rust std's APIs do. For example,
    /// there is no [`alloc::sync::Arc::get_mut`] or [`alloc::sync::Arc::make_mut`]
    /// under the assumption that the strong reference count becomes 1. We do
    /// offer consuming the [`DekoArc`] to get the inner value out and then re-wrap
    /// it back into a new [`DekoArc`]. This has only some ergnomic disadvantages.
    ///
    /// If one really needs interior mutability, one should wrap everything inside
    /// locks like [`Mutex`] or [`DekoRwLock`] and wrap data and permissions using
    /// [`DekoAtomicData<V, P>`].
    #[verifier::exec_allows_no_decreases_clause]
    pub fn clone(&self) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            r@ == self@,
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
                        data_perm: mut data_perm,
                    } = g;

                    count = inner_ref.count.load(Tracked(&mut atomic_count));

                    proof {
                        g = ArcStatus { count: atomic_count, data: token, data_perm: data_perm };
                    }
                }
            };

            if count == 0 {
                vstd::vpanic!("DekoArc use after free");
            }
            // Ensure that the reference count is valid.

            if count >= usize::MAX - 1 {
                // this is rare and the kernel should be buggy
                // so we just panic here.
                vstd::vpanic!("DekoArc reference count overflow");
            }
            let tracked mut new_reader = None;
            let res;
            open_atomic_invariant! {
                self.inv.borrow().borrow() => g => {
                    let tracked ArcStatus {
                        count: mut atomic_count,
                        data: mut token,
                        data_perm: mut data_perm,
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
                        g = ArcStatus { count: atomic_count, data: token, data_perm: data_perm };
                    }
                }
            };

            if res.is_ok() {
                return DekoArc {
                    ptr: self.ptr,  // ptr is Copy
                    inv: Tracked(self.inv.borrow().clone()),
                    inst: self.inst.clone(),
                    reader: Tracked(new_reader.tracked_unwrap()),
                    data: self.data,
                    ref_count: self.ref_count,
                    data_ptr: self.data_ptr,
                };
            }
        }
    }

    /// Try to write a new value into the inner data of this [`DekoArc`].
    /// If the strong reference count is 1, we can directly write
    /// into the inner data and return [`Result::Ok`] with the new [`DekoArc`]
    /// as well as the old value stored in the inner data.
    ///
    /// If the strong reference count is larger than 1, we return
    /// [`Result::Err`] with the provided value `v`.
    pub fn try_write(self, v: V) -> (r: Result<(Self, V), V>)
        requires
            self.wf(),
            self.inv(v),
            v.wf(),
        ensures
            match r {
                Result::Ok((new_arc, old_v)) => new_arc@ == v && old_v == self@,
                Result::Err(new_v) => v == new_v,
            },
    {
        proof {
            use_type_invariant(&self);
        }

        let DekoArc {
            ptr,
            inv,
            inst: Tracked(inst),
            reader: Tracked(reader),
            data,
            ref_count,
            data_ptr,
        } = self;

        let tracked perm = inst.reader_guard(reader.element(), &reader);
        let inner = ptr.borrow(Tracked(perm));
        let inner_ptr = inner.data;
        let count;
        let tracked mut inner_perm: Option<DekoPointsTo<ArcInner<V>>> = None;
        let tracked mut inner_data_perm: Option<DekoPointsTo<V>> = None;

        open_atomic_invariant! {
            inv.borrow().borrow() => g => {
                let tracked ArcStatus {
                    count: mut atomic_count,
                    data: mut token,
                    data_perm: mut data_perm,
                } = g;

                count = inner.count.compare_exchange_weak(Tracked(&mut atomic_count), 1, 0);
                proof {
                    if let Ok(1) = count {
                        let tracked (Tracked(arc_perm), _, _) = inst.do_free(reader.element(), &mut token, reader);
                        inner_perm = Some(arc_perm);
                        inner_data_perm = data_perm;

                        g = ArcStatus {
                            count: atomic_count,
                            data: token,
                            data_perm: None,
                        };
                    } else {
                        g = ArcStatus {
                            count: atomic_count,
                            data: token,
                            data_perm: data_perm,
                        };
                    }
                }
            }
        }

        if let Ok(1) = count {
            let tracked mut inner_data_perm = inner_data_perm.tracked_unwrap();
            let tracked mut inner_perm = inner_perm.tracked_unwrap();

            let old_v = inner_ptr.take(Tracked(&mut inner_data_perm));
            // Now construct a "new" DekoArc again.
            let new_self = Self::new_with_inner(
                inner_ptr,
                ptr,
                v,
                Tracked(inner_data_perm),
                Tracked(inner_perm),
                Ghost(inst.f()),
            );

            Ok((new_self, old_v))
        } else {
            Err(v)
        }
    }
}

} // verus!
