use vstd::assert_by_contradiction;
use vstd::map::*;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::simple_pptr::MemContents;

use crate::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
#[verifier::ext_equal]
pub struct Node<V: WellFormed> {
    /// The previous node in the linked list.
    pub prev: Option<DekoPPtr<Node<V>>>,
    /// The next node in the linked list.
    pub next: Option<DekoPPtr<Node<V>>>,
    pub value: V,
}

impl<T: WellFormed> View for Node<T> {
    type V = T;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.value
    }
}

#[verifier::reject_recursive_types(V)]
#[verifier::ext_equal]
pub tracked struct LinkedListInner<V: WellFormed> {
    pub ptrs: Seq<DekoPPtr<Node<V>>>,
    pub perms: Map<nat, DekoPointsTo<Node<V>>>,
}

#[verifier::reject_recursive_types(V)]
#[verifier::ext_equal]
pub struct LinkedList<V: WellFormed> {
    pub head: Option<DekoPPtr<Node<V>>>,
    pub tail: Option<DekoPPtr<Node<V>>>,
    pub inner: Tracked<LinkedListInner<V>>,
}

impl<V: WellFormed> LinkedList<V> {
    pub open spec fn prev(&self, i: nat) -> Option<DekoPPtr<Node<V>>> {
        if i == 0 {
            None
        } else {
            Some(self.inner@.ptrs[i as int - 1])
        }
    }

    pub open spec fn node_wf_at(&self, i: nat) -> bool {
        &&& self.inner@.perms[i].wf()
        &&& self.inner@.perms.dom().contains(i)
        &&& self.inner@.ptrs[i as int]@ == self.inner@.perms[i].pptr()
        &&& self.inner@.perms[i].mem_contents() matches MemContents::Init(node) && node.prev
            == self.prev(i) && node.next == self.next(i)
    }

    pub open spec fn node_wf(&self) -> bool {
        forall|i: nat| 0 <= i < self.inner@.ptrs.len() ==> #[trigger] self.node_wf_at(i)
    }

    pub open spec fn next(&self, i: nat) -> Option<DekoPPtr<Node<V>>> {
        if i == self.inner@.ptrs.len() as nat - 1 {
            None
        } else {
            Some(self.inner@.ptrs[i as int + 1])
        }
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& self.head.is_none()
        &&& self.tail.is_none()
        &&& self.inner@.ptrs.len() == 0
    }

    pub open spec fn spec_len(&self) -> nat {
        self.inner@.ptrs.len() as nat
    }

    pub proof fn spec_len_is_len(&self)
        requires
            self.wf(),
        ensures
            self.spec_len() == self@.len(),
    {
    }

    pub proof fn is_empty_implies_len_zero(&self)
        requires
            self.wf(),
        ensures
            self.is_empty() <==> self.spec_len() == 0,
    {
    }

    pub const fn new() -> (s: Self)
        ensures
            s.wf(),
    {
        Self {
            head: None,
            tail: None,
            inner: Tracked(
                LinkedListInner { ptrs: Seq::tracked_empty(), perms: Map::tracked_empty() },
            ),
        }
    }

    fn push_empty(&mut self, v: DekoPPtr<Node<V>>, perm: Tracked<DekoPointsTo<Node<V>>>)
        requires
            old(self).wf(),
            old(self)@.len() == 0,
            perm@.is_init(),
            perm@.wf(),
            perm@.value().value.wf(),
            perm@.value().prev == None::<DekoPPtr<Node<V>>>,
            perm@.value().next == None::<DekoPPtr<Node<V>>>,
            v@ == perm@.pptr(),
        ensures
            self.wf(),
            self@ =~= old(self)@.push(perm@.value().value),
            self.inner@.ptrs == old(self).inner@.ptrs.push(v),
    {
        self.tail = Some(v);
        self.head = Some(v);
        let Tracked(perm) = perm;

        // Update ghost states.
        proof {
            self.inner.borrow_mut().ptrs.tracked_push(v);
            self.inner.borrow_mut().perms.tracked_insert((self.inner@.ptrs.len() - 1) as _, perm);
        }
    }

    /// Pops the first element of the linked list.
    ///
    /// This API is marked `no_alloc` because it does not allocate any memory, and thus it
    /// requires the caller to manage the raw pointer; de-allocating it when it is no longer needed.
    pub fn pop_front_no_alloc(&mut self) -> (res: (
        DekoPPtr<Node<V>>,
        Tracked<DekoPointsTo<Node<V>>>,
    ))
        requires
            old(self).wf(),
            !old(self).is_empty(),
        ensures
            res.0 == old(self).inner@.ptrs.index(0),
            res.1@.value().value == old(self)@.index(0),
            self@ == old(self)@.remove(0),
            self.inner@.ptrs == old(self).inner@.ptrs.remove(0),
            self.wf(),
    {
        proof {
            // Unfold that definition so we indeed know that the head node is well formed.
            // so we can remove it from the permission map.
            assert(self.node_wf_at(0));
        }

        let head = self.head.unwrap();
        let tracked head_points_to = self.inner.borrow_mut().perms.tracked_remove(0);
        let v = head.borrow(Tracked(&mut head_points_to));

        match v.next {
            None => {
                self.head = None;
                self.tail = None;

                proof {
                    assert(self.inner@.ptrs.len() == 1);
                }
            },
            Some(next) => {
                assert(old(self)@.len() > 1);
                assert(old(self).node_wf_at(1));  // for dom().contains(1).

                self.head = Some(next);
                let tracked mut next_points_to = self.inner.borrow_mut().perms.tracked_remove(1);

                // Modify the next node so that its prev becomes None and it should be the head node.
                let mut next_node = next.take(Tracked(&mut next_points_to));
                next_node.prev = None;
                next.write(Tracked(&mut next_points_to), next_node);

                // Now we update the ghost states.
                proof {
                    // We update the points to map.
                    self.inner.borrow_mut().perms.tracked_insert(1, next_points_to);

                    // Now update the permission map by shifting the keys.
                    assert forall|i: nat|
                        1 <= i < old(self)@.len() implies self.inner@.perms.dom().contains(i) by {
                        assert(old(self).node_wf_at(i));
                    }

                    // Update keys. => self.index(j) == old(self).index(key_map.index(i + 1)) by left.
                    self.inner.borrow_mut().perms.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |i: nat| 0 <= i && i < old(self)@.len() - 1,
                            |i: nat| (i + 1) as nat,
                        ),
                    );
                }
            },
        }

        // Update pointers.
        proof {
            // let this = self.inner.borrow_mut().ptrs.tracked_remove(0);
            // self.inner.borrow_mut().ptrs = (self)@.remove(0);
            self.inner.borrow_mut().ptrs.tracked_pop_front();

            if self.inner@.ptrs.len() > 0 {
                assert(self.node_wf_at(0));
                assert(forall|i: nat|
                    0 < i < self@.len() && old(self).node_wf_at(i + 1)
                        ==> #[trigger] self.node_wf_at(i));

                assert forall|i: int| 0 <= i && i < self@.len() implies #[trigger] self@[i] == old(
                    self,
                )@.subrange(1, old(self)@.len() as int)[i] by {
                    assert(old(self).node_wf_at(i as nat + 1));
                };
                assert(self@ =~= old(self)@.remove(0));
                assert(self.tail == Some(self.inner@.ptrs[self.inner@.ptrs.len() as int - 1]));
                assert(self.head == Some(self.inner@.ptrs[0]));
            } else {
                assert(self.wf());
            }
        }

        (head, Tracked(head_points_to))
    }

    /// Pushes to the front of the linked list without allocating any memory.
    pub fn push_front_no_alloc(
        &mut self,
        v: DekoPPtr<Node<V>>,
        perm: Tracked<DekoPointsTo<Node<V>>>,
    )
        requires
            old(self).wf(),
            perm@.wf(),
            perm@.value().value.wf(),
            v@ == perm@.pptr(),
            perm@.is_init(),
        ensures
            self.wf(),
            self@ == seq![perm@.value().value].add(old(self)@),
            self.inner@.ptrs == seq![v].add(old(self).inner@.ptrs),
    {
        let Tracked(mut points_to) = perm;
        let val = v.take(Tracked(&mut points_to));
        match self.head {
            None => {
                v.write(Tracked(&mut points_to), Node { prev: None, next: None, value: val.value });

                self.push_empty(v, Tracked(points_to));
            },
            Some(old_head_ptr) => {
                proof {
                    assert(self.inner@.ptrs.len() > 0);
                    assert(self.node_wf_at(0));
                }

                // Now we update the node pointers.
                v.write(
                    Tracked(&mut points_to),
                    Node { prev: None, next: Some(old_head_ptr), value: val.value },
                );

                assert(self.inner@.perms.dom().contains(0));
                let tracked mut old_head_points_to = self.inner.borrow_mut().perms.tracked_remove(
                    0,
                );
                assert(!self.inner@.perms.dom().contains(0));
                let mut old_head_node = old_head_ptr.take(Tracked(&mut old_head_points_to));
                old_head_node.prev = Some(v);
                old_head_ptr.write(Tracked(&mut old_head_points_to), old_head_node);
                proof {
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(0, old_head_points_to);
                }
                self.head = Some(v);

                // Simultaneously, we update the ghost states.
                proof {
                    assert forall|i: nat|
                        0 <= i < old(
                            self,
                        ).inner@.ptrs.len() implies self.inner@.perms.dom().contains(i) by {
                        assert(old(self).node_wf_at(i));
                    }

                    // Update keys.
                    self.inner.borrow_mut().perms.tracked_map_keys_in_place(
                        Map::<nat, nat>::new(
                            |i: nat| 1 <= i <= old(self)@.len() as nat,
                            |i: nat| (i - 1) as nat,
                        ),  // self.index(j) == old(self).index(key_map.index(j))
                    );

                    self.inner.borrow_mut().ptrs.tracked_insert(0, v);
                    self.inner.borrow_mut().perms.tracked_insert(0, points_to);

                    assert(self@ =~= seq![perm@.value().value].add(old(self)@));
                    assert(self.node_wf_at(0));
                    // Some additional proofs on wellformed.
                    assert(forall|i: nat|
                        1 <= i && i <= old(self).inner@.ptrs.len() && old(self).node_wf_at(
                            (i - 1) as nat,
                        ) ==> #[trigger] self.node_wf_at(i));
                    assert forall|i: int|
                        1 <= i && i <= self.inner@.ptrs.len() as int - 1 implies #[trigger] old(
                        self,
                    ).inner@.ptrs.index(i - 1) == self.inner@.ptrs.index(i) by {
                        assert(old(self).node_wf_at((i - 1) as nat));
                    }

                    assert(self.node_wf_at(1));
                }
            },
        }
    }
}

impl<V: WellFormed> WellFormed for LinkedList<V> {
    /// TODO: Add an axiom for this self@.len() == self.inner@.ptrs.len().
    /// If this is missing the trigger cannot be automatically matches by Verus
    open spec fn wf(&self) -> bool {
        &&& self.node_wf()
        &&& if self.inner@.ptrs.len() == 0 {
            &&& self.head.is_none()
            &&& self.tail.is_none()
        } else {
            &&& self.head == Some(self.inner@.ptrs[0])
            &&& self.tail == Some(self.inner@.ptrs[self.inner@.ptrs.len() as int - 1])
        }
    }
}

impl<T: WellFormed> View for LinkedList<T> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Self::V {
        Seq::new(self.inner@.ptrs.len(), |i: int| self.inner@.perms[i as nat].value().value)
    }
}

impl<T: WellFormed> DeepView for LinkedList<T> {
    type V = Seq<DekoPPtr<Node<T>>>;

    /// This allows us to view the linked list as a sequence of pointers to nodes.
    open spec fn deep_view(&self) -> Self::V {
        self.inner@.ptrs
    }
}

/// A wrapper around `LinkedList` that provides a more convenient API for
/// manipulating the linked list. This is intended to be used as a closure.
pub fn pop_front_closure<V: WellFormed>(ll: LinkedList<V>) -> (res: (
    (DekoPPtr<Node<V>>, Tracked<DekoPointsTo<Node<V>>>),
    LinkedList<V>,
))
    requires
        ll.wf(),
        !ll.is_empty(),
    ensures
        res.0.0 == ll.inner@.ptrs.index(0),
        res.0.1@.value().value == ll@.index(0),
        ll@.remove(0) == res.1@,
        res.1.wf(),
        res.1@.len() == ll@.len() - 1,
        res.1.inner@.ptrs == ll.inner@.ptrs.remove(0),
{
    let mut ll = ll;
    let hd = ll.pop_front_no_alloc();

    (hd, ll)
}

} // verus!
