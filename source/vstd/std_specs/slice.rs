use super::super::prelude::*;
use super::cmp::*;
use super::core::IndexSetTrustedSpec;
use super::core::TrustedSpecSealed;
use verus_builtin::*;

use core::cmp::Ordering;
use core::slice::Iter;

use verus as verus_;

verus_! {

pub open spec fn spec_slice_is_sorted<T: PartialOrd>(s: &[T]) -> bool {
    forall |i: int, j: int|
        #![trigger s@[i], s@[j]]
            0 <= i < j < s@.len() ==> s@[i].partial_cmp_spec(&s@[j]) == Some(Ordering::Less,)
}

#[verifier::when_used_as_spec(spec_slice_is_sorted)]
pub assume_specification<T: PartialOrd> [ <[T]>::is_sorted ] (s: &[T]) -> (r: bool)
    ensures
        r == spec_slice_is_sorted(s),
;

pub assume_specification<T: Ord> [ <[T]>::binary_search ] (s: &[T], x: &T) -> (r: Result<usize, usize>)
    ensures
        s.is_sorted() ==>
            match r {
                Ok(index) => 0 <= index < s@.len() && s@[index as int] == *x,
                Err(index) => 0 <= index <= s@.len() &&
                    (index == 0 || s@[index - 1].cmp_spec(x) == Ordering::Less) &&
                    (index == s@.len() || s@[index as int].cmp_spec(x) == Ordering::Greater),
            }
        ,
;

pub assume_specification<'a, T, F> [ <[T]>::binary_search_by ] (s: &'a [T], mut f: F) -> (r: Result<usize, usize>)
    where
        F: FnMut(&'a T) -> Ordering,
    ensures
        match r {
            Ok(index) => 0 <= index < s@.len(),
            Err(index) => 0 <= index <= s@.len() 
        }
;

impl<T, const N: usize> TrustedSpecSealed for [T; N] {}

impl<T, const N: usize> IndexSetTrustedSpec<usize> for [T; N] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < N
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ === self@.update(index as int, val)
    }
}

impl<T> TrustedSpecSealed for [T] {}

impl<T> IndexSetTrustedSpec<usize> for [T] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < self@.len()
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ == self@.update(index as int, val)
    }
}

// The `iter` method of a `<T>` returns an iterator of type `Iter<'_, T>`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIter<'a, T: 'a>(Iter<'a, T>);

impl<T> View for Iter<'_, T> {
    type V = (int, Seq<T>);

    uninterp spec fn view(&self) -> (int, Seq<T>);
}

impl<T: DeepView> DeepView for Iter<'_, T> {
    type V = (int, Seq<T::V>);

    open spec fn deep_view(&self) -> Self::V {
        let (i, v) = self@;
        (i, Seq::new(v.len(), |i: int| v[i].deep_view()))
    }
}

pub assume_specification<'a, T>[ Iter::<'a, T>::next ](elements: &mut Iter<'a, T>) -> (r: Option<
    &'a T,
>)
    ensures
        ({
            let (old_index, old_seq) = old(elements)@;
            match r {
                None => {
                    &&& elements@ == old(elements)@
                    &&& old_index >= old_seq.len()
                },
                Some(element) => {
                    let (new_index, new_seq) = elements@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& element == old_seq[old_index]
                },
            }
        }),
;

pub struct IterGhostIterator<'a, T> {
    pub pos: int,
    pub elements: Seq<T>,
    pub phantom: Option<&'a T>,
}

impl<'a, T> super::super::pervasive::ForLoopGhostIteratorNew for Iter<'a, T> {
    type GhostIter = IterGhostIterator<'a, T>;

    open spec fn ghost_iter(&self) -> IterGhostIterator<'a, T> {
        IterGhostIterator { pos: self@.0, elements: self@.1, phantom: None }
    }
}

impl<'a, T: 'a> super::super::pervasive::ForLoopGhostIterator for IterGhostIterator<'a, T> {
    type ExecIter = Iter<'a, T>;

    type Item = T;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Iter<'a, T>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.elements == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.elements == self.elements
            &&& 0 <= self.pos <= self.elements.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.elements.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.elements.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<T> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Iter<'a, T>) -> IterGhostIterator<'a, T> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, T> View for IterGhostIterator<'a, T> {
    type V = Seq<T>;

    open spec fn view(&self) -> Seq<T> {
        self.elements.take(self.pos)
    }
}

// To allow reasoning about the ghost iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: s.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_slice_iter)` to the specification for
// the executable `into_iter` method and define that spec function here.
pub uninterp spec fn spec_slice_iter<'a, T>(s: &'a [T]) -> (iter: Iter<'a, T>);

pub broadcast proof fn axiom_spec_slice_iter<'a, T>(s: &'a [T])
    ensures
        (#[trigger] spec_slice_iter(s))@ == (0int, s@),
{
    admit();
}

#[verifier::when_used_as_spec(spec_slice_iter)]
pub assume_specification<'a, T>[ <[T]>::iter ](s: &'a [T]) -> (iter: Iter<'a, T>)
    ensures
        ({
            let (index, seq) = iter@;
            &&& index == 0
            &&& seq == s@
        }),
;

pub broadcast group group_slice_axioms {
    axiom_spec_slice_iter,
}

} // verus!
