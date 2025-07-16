use vstd::map::*;
use vstd::prelude::*;
use vstd::raw_ptr::Dealloc;
use vstd::simple_pptr::MemContents;

use crate::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
pub struct Node<V: WellFormed> {
    /// The previous node in the linked list.
    prev: Option<DekoPPtr<Node<V>>>,
    /// The next node in the linked list.
    next: Option<DekoPPtr<Node<V>>>,
    value: V,
}

impl<T: WellFormed> View for Node<T> {
    type V = T;

    closed spec fn view(&self) -> Self::V {
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
    inner: Tracked<LinkedListInner<V>>,
}

impl<V: WellFormed> LinkedList<V> {
    pub closed spec fn prev(&self, i: nat) -> Option<DekoPPtr<Node<V>>> {
        if i == 0 {
            None
        } else {
            Some(self.inner@.ptrs[i as int - 1])
        }
    }

    pub closed spec fn node_wf_at(&self, i: nat) -> bool {
        &&& self.inner@.perms[i].wf()
        &&& self.inner@.perms.dom().contains(i)
        &&& self.inner@.ptrs[i as int]@ == self.inner@.perms[i].pptr()
        &&& self.inner@.perms[i].mem_contents() matches MemContents::Init(node) && node.prev
            == self.prev(i) && node.next == self.next(i)
    }

    pub closed spec fn node_wf(&self) -> bool {
        forall|i: int| 0 <= i < self@.len() ==> #[trigger] self.node_wf_at(i as nat)
    }

    pub closed spec fn next(&self, i: nat) -> Option<DekoPPtr<Node<V>>> {
        if i == self.inner@.ptrs.len() as nat - 1 {
            None
        } else {
            Some(self.inner@.ptrs[i as int + 1])
        }
    }

    pub closed spec fn is_empty(&self) -> bool {
        &&& self.head.is_none()
        &&& self.tail.is_none()
        &&& self.inner@.ptrs.len() == 0
        &&& self.inner@.perms.len() == 0
    }

    pub closed spec fn spec_len(&self) -> nat {
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

    // /// Pushes to the end of the linked list without allocating any memory.
    // pub fn push_no_alloc(&mut self, v: DekoPPtr<Node<V>>, Tracked(perm): Tracked<DekoPointsTo<Node<V>>>)
    // requires
    //     old(self).wf(),
    //     v@ == perm.pptr(),
    //     perm.is_init(),
    // ensures
    //     self.wf(),
    //     self@ = old(self)@.push(perm.value().value),
    // {

    // }

    // pub fn push(&mut self, v: V, allocator: &DefaultDekoHeapAllocator)
    // requires
    //     allocator.wf(),
        
    // {
        
    // }
}

impl<V: WellFormed> WellFormed for LinkedList<V> {
    closed spec fn wf(&self) -> bool {
        &&& if self@.len() == 0 {
            &&& self.head.is_none()
            &&& self.tail.is_none()
            &&& self.inner@.ptrs.len() == 0
            &&& self.inner@.perms.len() == 0
        } else {
            &&& self.head == Some(self.inner@.ptrs[0])
            &&& self.tail == Some(self.inner@.ptrs[self.inner@.ptrs.len() as int - 1])
            &&& self.inner@.ptrs.len() == self.inner@.perms.len()
            &&& self.node_wf()
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
