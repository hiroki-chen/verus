use vstd::assert_by_contradiction;
use vstd::map::*;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::simple_pptr::MemContents;

use crate::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
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
pub tracked struct LinkedListInner<V: WellFormed> {
    pub ptrs: Seq<DekoPPtr<Node<V>>>,
    pub perms: Map<nat, DekoPointsTo<Node<V>>>,
}

#[verifier::reject_recursive_types(V)]
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
        &&& self.inner@.perms.len() == 0
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
                        ), // self.index(j) == old(self).index(key_map.index(j))
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
                    assert(self.wf());
                }
            },
        }
    }
}

impl<V: WellFormed> WellFormed for LinkedList<V> {
    closed spec fn wf(&self) -> bool {
        &&& self.node_wf()
        &&& if self.inner@.ptrs.len() == 0 {
            &&& self.head.is_none()
            &&& self.tail.is_none()
            &&& self.inner@.ptrs.len() == 0
            &&& self.inner@.perms.len() == 0
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

} // verus!
