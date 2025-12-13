use vstd::prelude::*;

use crate::mm::frame_allocator::DekoAllocatorApi;

verus! {

/// A type alias for a vector that uses the Deko page frame allocator as its allocator.
///
/// For common slice-like functions please call [`Vec::as_slice`] to get a slice reference which
/// guarantees that the underlying [`View`] of the vector will be the same as `[T]`
///
/// # Special Notes
///
/// Some lemmas and proofs imported directly from `vstd` will broken as [`alloc::vec::Vec<T>`] is
/// _not_ the same thing as [`alloc::vec::Vec<T, A>`].
pub type Vec<T> = alloc::vec::Vec<T, DekoAllocatorApi>;

/// A type alias for a vector declaration that uses the Deko page frame allocator as its allocator.
pub type VecDeque<T> = alloc::collections::vec_deque::VecDeque<T, DekoAllocatorApi>;

/// Updates the element at the given index in the vector to the given value.
///
/// Since Verus does not support mutable references to elements in a vector,
/// we provide this helper function to update an element at a specific index.
#[verifier::external_body]
#[inline]
pub fn update_vec<T>(v: &mut Vec<T>, index: usize, value: T)
    requires
        0 <= index < old(v)@.len(),
    ensures
        v@ =~= old(v)@.update(index as int, value),
{
    v[index] = value;
}

} // verus!
/// Creates a [`Vec`] containing the arguments.
///
/// `vec!` allows `Vec`s to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
#[macro_export]
macro_rules! vec {
    ($($x:expr),* $(,)?) => {
        {
            let allocator = $crate::mm::frame_allocator::DekoAllocatorApi {  };
            let mut temp_vec = $crate::collections::Vec::new_in(allocator);
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
    ($val:expr; $count:expr) => {
        {
            let allocator = $crate::mm::frame_allocator::DekoAllocatorApi {  };
            let mut temp_vec = $crate::collections::Vec::new_in(allocator);
            temp_vec.resize($count, $val);
            temp_vec
        }
    };

    () => {
        {
            let allocator = $crate::mm::frame_allocator::DekoAllocatorApi {  };
            $crate::collections::Vec::new_in(allocator)
        }
    };
}
