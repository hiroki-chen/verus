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

    open spec fn view(&self) -> Self::V {
        self.value
    }
}

impl<V: WellFormed> WellFormed for Node<V> {
    open spec fn wf(&self) -> bool {
        &&& self@.wf()
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
    pub len: usize,
}

impl<V: WellFormed> LinkedList<V> {
    pub open spec fn prev(&self, i: nat) -> Option<DekoPPtr<Node<V>>> {
        if i == 0 {
            None
        } else {
            Some(self.inner@.ptrs[i as int - 1])
        }
    }

    pub broadcast proof fn lemma_length_is_ptr_len(&self)
        requires
            self.wf(),
        ensures
            self@.len() == #[trigger] self.inner@.ptrs.len(),
    {
        assert(self.inner@.ptrs.len() as nat == self@.len());
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
            s.is_empty(),
            s@.len() == 0,
    {
        Self {
            head: None,
            tail: None,
            inner: Tracked(
                LinkedListInner { ptrs: Seq::tracked_empty(), perms: Map::tracked_empty() },
            ),
            len: 0,
        }
    }

    #[inline(always)]
    pub fn len(&self) -> (len: usize)
        requires
            self.wf(),
        ensures
            len == self@.len(),
            len == self.spec_len(),
    {
        self.len
    }

    fn push_empty(&mut self, v: DekoPPtr<Node<V>>, perm: Tracked<DekoPointsTo<Node<V>>>)
        requires
            old(self).wf(),
            old(self)@.len() == 0,
            perm@.is_init(),
            perm@.wf(),
            perm@.value().wf(),
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
        self.len = self.len + 1;

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
            res.0@ == res.1@.pptr(),
            res.1@.wf(),
            res.1@.is_init(),
    {
        proof {
            // Unfold that definition so we indeed know that the head node is well formed.
            // so we can remove it from the permission map.
            assert(self.node_wf_at(0));
        }

        self.len = self.len - 1;
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

    /// Removes the element at the given index from the linked list.
    ///
    /// This is the slowest part of a primitive buddy allocator, because it runs in
    /// O(log N) time where N is the number of blocks of a given size.
    pub fn remove(&mut self, i: usize) -> (ret: (DekoPPtr<Node<V>>, Tracked<DekoPointsTo<Node<V>>>))
        requires
            old(self).wf(),
            0 <= i < old(self).inner@.ptrs.len(),
            !old(self).is_empty(),
        ensures
            ret.0 == old(self).inner@.ptrs.index(i as int),
            ret.1@.value().value == old(self)@.index(i as int),
            self@ =~= old(self)@.remove(i as int),
            self.inner@.ptrs == old(self).inner@.ptrs.remove(i as int),
            self.wf(),
    {
        // If we are removing the first element, we can use the pop_front_no_alloc method.
        if i == 0 {
            return self.pop_front_no_alloc();
        }
        let mut idx = 0;
        let mut ptr = self.head;

        while idx < i - 1
            invariant
                idx < i < self.inner@.ptrs.len(),
                forall|j: nat| 0 <= j < self.inner@.ptrs.len() ==> #[trigger] self.node_wf_at(j),
                ptr matches Some(p) && p == self.inner@.ptrs[idx as int],
            decreases i - idx,
        {
            proof {
                assert(self.node_wf_at(idx as nat));
            }
            // Get the current node.
            let tracked perm = self.inner.borrow().perms.tracked_borrow(idx as nat);
            let p = ptr.unwrap().borrow(Tracked(perm));

            ptr = p.next;
            idx += 1;
        }

        proof {
            // Now we have ptr == self@[idx] as prev and ptr->next == self@[idx + 1] as this.
            assert(self.wf());
            assert(self.node_wf_at(idx as nat));
            assert(self.node_wf_at((idx + 1) as nat));
        }
        let tracked prev_perm = self.inner.borrow().perms.tracked_borrow(idx as nat);
        let tracked this_perm = self.inner.borrow().perms.tracked_borrow((idx + 1) as nat);

        let prev_node = ptr.unwrap();
        let prev_node_v = prev_node.borrow(Tracked(prev_perm));
        let this_node = prev_node_v.next.unwrap();
        let this_node_v = this_node.borrow(Tracked(this_perm));

        match this_node_v.next {
            // If we have next then we have to update the prev pointer.
            Some(next_node) => {
                proof {
                    assert(self.wf());
                    assert(self.node_wf_at((idx + 2) as nat));
                }

                let tracked mut prev_perm = self.inner.borrow_mut().perms.tracked_remove(
                    idx as nat,
                );
                let tracked mut this_perm = self.inner.borrow_mut().perms.tracked_remove(
                    (idx + 1) as nat,
                );
                let tracked mut next_perm = self.inner.borrow_mut().perms.tracked_remove(
                    (idx + 2) as nat,
                );

                let mut prev_node_v = prev_node.take(Tracked(&mut prev_perm));
                let mut next_node_v = next_node.take(Tracked(&mut next_perm));
                prev_node_v.next = Some(next_node);
                next_node_v.prev = Some(prev_node);

                prev_node.write(Tracked(&mut prev_perm), prev_node_v);
                next_node.write(Tracked(&mut next_perm), next_node_v);
                self.len = self.len - 1;

                // node -> prev    -> this     -> next -> node
                //         ^idx        ^idx + 1   ^ idx + 2
                // node -> prev    -> next     -> node
                //        ^idx        ^idx + 2
                proof {
                    assert(idx + 1 == i);
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(idx as nat, prev_perm);
                    self.inner.borrow_mut().perms.tracked_insert((idx + 2) as nat, next_perm);
                    self.inner.borrow_mut().ptrs.tracked_remove((idx + 1) as int);

                    assert forall|i: nat|
                        (0 <= i <= idx) || (idx + 2 <= i < old(
                            self,
                        )@.len()) implies self.inner@.perms.dom().contains(i) by {
                        assert(old(self).node_wf_at(i));
                    };

                    // Now we need to shift the key map
                    // [    ] | [    ]
                    //  keep   shift by 1
                    let ghost mut keys_left = Map::new(
                        |i: nat| 0 <= i <= idx as nat,
                        |i: nat| i as nat,
                    );
                    let ghost keys_right = Map::new(
                        |i: nat| idx + 1 <= i < old(self)@.len() - 1,
                        |i: nat| (i + 1) as nat,
                    );

                    let ghost keys = keys_left.union_prefer_right(keys_right);
                    self.inner.borrow_mut().perms.tracked_map_keys_in_place(keys);

                    assert forall|i: nat| (0 <= i <= idx) implies self.node_wf_at(i) by {
                        assert(old(self).node_wf_at(i));
                    };
                    assert forall|i: nat| (idx + 1 <= i < self@.len()) implies self.node_wf_at(
                        i,
                    ) by {
                        assert(old(self).node_wf_at(i + 1));
                    };
                }

                (this_node, Tracked(this_perm))
            },
            None => {
                self.tail = Some(prev_node);
                let tracked mut prev_perm = self.inner.borrow_mut().perms.tracked_remove(
                    idx as nat,
                );
                let tracked mut this_perm = self.inner.borrow_mut().perms.tracked_remove(
                    (idx + 1) as nat,
                );

                let mut prev_node_v = prev_node.take(Tracked(&mut prev_perm));
                prev_node_v.next = None;
                prev_node.write(Tracked(&mut prev_perm), prev_node_v);
                self.len = self.len - 1;

                proof {
                    assert(prev_node == old(self).inner@.ptrs.index(idx as int));
                    assert(idx + 1 == old(self)@.len() - 1);
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(idx as nat, prev_perm);
                    self.inner.borrow_mut().ptrs.tracked_remove((idx + 1) as int);

                    assert forall|i: nat|
                        0 <= i < self.inner@.ptrs.len() implies #[trigger] self.node_wf_at(i) by {
                        assert(old(self).node_wf_at(i as nat));
                    }
                }

                (this_node, Tracked(this_perm))
            },
        }
    }

    /// Finds a block by its address in the linked list and returns its index if it exists.
    pub fn find_by_addr(&self, addr: u64) -> (res: Option<usize>)
        requires
            self.wf(),
        ensures
            res matches Some(idx) ==> 0 <= idx < self.inner@.ptrs.len()
                && self.inner@.ptrs[idx as int].addr() == addr as usize,
    {
        let mut ptr = self.head.as_ref();
        let mut idx = 0;

        loop
            invariant
                self.wf(),
                idx < self.inner@.ptrs.len() ==> {
                    &&& ptr matches Some(ptr)
                    &&& ptr == self.inner@.ptrs[idx as int]
                },
            decreases self.inner@.ptrs.len() as usize - idx,
        {
            if ptr.is_none() || idx >= self.len {
                return None;
            }
            let p = ptr.unwrap();
            if p.addr() == addr as usize {
                return Some(idx);
            }
            proof {
                assert(self.node_wf_at(idx as nat));
            }

            let tracked perm = self.inner.borrow().perms.tracked_borrow(idx as nat);
            let p = p.borrow(Tracked(perm));

            idx += 1;
            ptr = p.next.as_ref();
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
            old(self)@.len() < usize::MAX,
            perm@.wf(),
            perm@.value().wf(),
            perm@.is_init(),
            v@ == perm@.pptr(),
        ensures
            self.wf(),
            self@ =~= old(self)@.insert(0, perm@.value().value),
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
                self.len = self.len + 1;

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
                        1 <= i <= old(self).inner@.ptrs.len() && old(self).node_wf_at(
                            (i - 1) as nat,
                        ) ==> #[trigger] self.node_wf_at(i));
                    assert forall|i: int|
                        1 <= i <= self.inner@.ptrs.len() as int - 1 implies #[trigger] old(
                        self,
                    ).inner@.ptrs.index(i - 1) == self.inner@.ptrs.index(i) by {
                        assert(old(self).node_wf_at((i - 1) as nat));
                    }

                    assert(self.node_wf_at(1));
                }
            },
        }
    }

    pub fn push_back_no_alloc(&mut self, v: DekoPPtr<Node<V>>, perm: Tracked<DekoPointsTo<Node<V>>>)
        requires
            old(self).wf(),
            old(self)@.len() < usize::MAX,
            perm@.wf(),
            perm@.value().wf(),
            perm@.is_init(),
            v@ == perm@.pptr(),
        ensures
            self.wf(),
            self@ =~= old(self)@.insert(old(self)@.len() as int, perm@.value().value),
            self.inner@.ptrs == (old(self).inner@.ptrs).add(seq![v]),
    {
        let Tracked(mut points_to) = perm;
        let val = v.take(Tracked(&mut points_to));

        match self.tail {
            None => {
                v.write(Tracked(&mut points_to), Node { prev: None, next: None, value: val.value });

                self.push_empty(v, Tracked(points_to));
            },
            Some(old_tail_ptr) => {
                proof {
                    assert(self.inner@.ptrs.len() > 0);
                    assert(self.node_wf_at((self.inner@.ptrs.len() - 1) as nat));
                }
                self.len = self.len + 1;

                // Now we update the node pointers.
                v.write(
                    Tracked(&mut points_to),
                    Node { prev: Some(old_tail_ptr), next: None, value: val.value },
                );

                assert(self.inner@.perms.dom().contains((self.inner@.ptrs.len() - 1) as nat));
                let tracked mut old_tail_points_to = self.inner.borrow_mut().perms.tracked_remove(
                    (self.inner@.ptrs.len() - 1) as nat,
                );
                assert(!self.inner@.perms.dom().contains((self.inner@.ptrs.len() - 1) as nat));
                let mut old_tail_node = old_tail_ptr.take(Tracked(&mut old_tail_points_to));
                old_tail_node.next = Some(v);
                old_tail_ptr.write(Tracked(&mut old_tail_points_to), old_tail_node);
                proof {
                    // Update the ghost states.
                    self.inner.borrow_mut().perms.tracked_insert(
                        (self.inner@.ptrs.len() - 1) as nat,
                        old_tail_points_to,
                    );
                }
                self.tail = Some(v);

                // Simultaneously, we update the ghost states.
                // This is simpler than push_front because we do not need to shift any keys.
                proof {
                    self.inner.borrow_mut().ptrs.tracked_push(v);
                    self.inner.borrow_mut().perms.tracked_insert(
                        (self.inner@.ptrs.len() - 1) as nat,
                        points_to,
                    );

                    assert(self@ =~= old(self)@.insert(
                        old(self)@.len() as int,
                        perm@.value().value,
                    ));
                    assert(self.node_wf_at((self.inner@.ptrs.len() - 1) as nat));
                    assert(forall|i: nat|
                        0 <= i <= old(self).inner@.ptrs.len() && old(self).node_wf_at(i)
                            ==> #[trigger] self.node_wf_at(i));
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
        &&& self.len == self.inner@.ptrs.len()
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

pub fn remove_closure<V: WellFormed>(ll: LinkedList<V>, i: usize) -> (res: (
    (DekoPPtr<Node<V>>, Tracked<DekoPointsTo<Node<V>>>),
    LinkedList<V>,
))
    requires
        ll.wf(),
        0 <= i < ll.inner@.ptrs.len(),
        !ll.is_empty(),
    ensures
        res.0.0 == ll.inner@.ptrs.index(i as int),
        res.0.1@.value().value == ll@.index(i as int),
        ll@.remove(i as int) == res.1@,
        res.1.wf(),
        res.1.inner@.ptrs == ll.inner@.ptrs.remove(i as int),
{
    let mut ll = ll;
    let hd = ll.remove(i);

    (hd, ll)
}

} // verus!
