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
///
/// Most of the APIs are defined on the auto-djusted slice type `[T]`, so you can call those APIs
/// after converting the vector to a slice via [`Vec::as_slice`] or just call `&`.
pub type Vec<T> = alloc::vec::Vec<T, DekoAllocatorApi>;

/// A type alias for a vector declaration that uses the Deko page frame allocator as its allocator.
pub type VecDeque<T> = alloc::collections::vec_deque::VecDeque<T, DekoAllocatorApi>;

/// A UTF-8 string that uses the Deko page frame allocator as its allocator.
pub type String = deko_std::std_extra::string::String<DekoAllocatorApi>;

/// Wrapper around [`[T]::get_unchecked`] for slices.
///
/// The trait implementation in core is not directly usable in Verus.
///
/// This function can be used for performance critical code where the
/// caller can guarantee that the index is in bounds, and wants to avoid
/// the overhead of bounds checking.
#[inline(always)]
#[track_caller]
#[verifier::external_body]
#[verus_spec(r =>
    requires
        0 <= index < v@.len(),
    ensures
        r == v@[index as int],
)]
pub fn get_unchecked<T>(v: &[T], index: usize) -> &T {
    // SAFETY: Precondition ensures that this never goes out of bounds.
    unsafe { v.get_unchecked(index) }
}

/// Updates the element at the given index in the vector to the given value.
///
/// Since Verus does not support mutable references to elements in a vector,
/// we provide this helper function to update an element at a specific index.
#[inline]
#[verifier::external_body]
pub fn update_vec<T>(v: &mut Vec<T>, index: usize, value: T)
    requires
        0 <= index < old(v)@.len(),
    ensures
        final(v)@ =~= old(v)@.update(index as int, value),
{
    v[index] = value;
}

#[inline]
#[verifier(external_body)]
pub fn update_slice<T, const N: usize>(s: &mut [T; N], index: usize, value: T)
    requires
        0 <= index < old(s)@.len(),
    ensures
        final(s)@ =~= old(s)@.update(index as int, value),
{
    s[index] = value;
}

} // verus!
/// Creates a [`Vec`] containing the arguments.
///
/// [`vec!`] allows [`Vec`]s to be defined with the same syntax as array expressions.
/// There are three forms of this macro:
///
/// 1. `vec![elem1, elem2, ...]` - creates a vector containing the given elements.
/// 2. `vec![elem; count]` - creates a vector containing `count` copies of `elem`.
/// 3. `vec![]` - creates an empty vector
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
