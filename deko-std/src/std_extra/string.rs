use alloc::vec::Vec;

use vstd::prelude::*;

use crate::fmt::{DekoDebug, DekoWriter};
use crate::wf::WellFormed;

verus! {

/// A UTF-8–encoded, growable string.
///
/// String is the most common string type. It has ownership over the contents of the string,
/// stored in a heap-allocated buffer (see Representation). It is closely related to its borrowed
/// counterpart, the primitive [`str`].
///
/// This type extends the standard library's `String` type with support for custom allocators,
/// and is designed to be used in contexts where the standard library's `String` type is not
/// available (e.g., `no_std` environments). It provides a subset of the functionality of the
/// standard library's `String` type, focusing on core string manipulation capabilities while
/// ensuring compatibility with the [`core::alloc::Allocator`] trait. The implementation of this
/// type is designed to be verified using the Verus verification tool, and includes specifications
/// and proofs to ensure its correctness and safety properties. The `String` type is defined as a
/// struct that contains a [`Vec<u8, A>`], where `A` is a type that implements the [`core::alloc::Allocator`]
/// trait. The [`Vec<u8, A>`] is used to store the UTF-8 encoded bytes of the string, and the `String`
/// type provides methods for creating, manipulating, and querying the string, as well as implementing
/// traits such as [`Deref`], [`Clone`], [`PartialEq`], and [`Eq`].
///
/// [`Deref`]: core::ops::Deref
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
#[derive(Hash)]
pub struct String<A: core::alloc::Allocator> {
    bytes: Vec<u8, A>,
}

impl<A: core::alloc::Allocator> View for String<A> {
    type V = Seq<char>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<A: core::alloc::Allocator> DeepView for String<A> {
    type V = Seq<char>;

    #[verifier::inline]
    open spec fn deep_view(&self) -> Self::V {
        self@
    }
}

impl<A: core::alloc::Allocator> WellFormed for String<A> {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        true
    }
}

pub uninterp spec fn string_is_ascii_spec<A: core::alloc::Allocator>(s: &String<A>) -> bool;

#[verus_verify]
impl<A: core::alloc::Allocator> String<A> {
    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r@ == Seq::<char>::empty(),
            string_is_ascii_spec(&r),
    )]
    pub fn new_in(alloc: A) -> Self {
        Self { bytes: Vec::new_in(alloc) }
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r@ == Seq::<char>::empty(),
            string_is_ascii_spec(&r),
    )]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self { bytes: Vec::with_capacity_in(capacity, alloc) }
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r as int == self@.len(),
    )]
    pub fn char_len(&self) -> usize {
        self.as_str().chars().count()
    }

    #[inline]
    #[verifier::external_body]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    #[verifier::external_body]
    pub fn capacity(&self) -> usize {
        self.bytes.capacity()
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r <==> self@.len() == 0,
    )]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r@ == self@,
            r.is_ascii() == string_is_ascii_spec(self),
    )]
    pub fn as_str(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(self.bytes.as_slice()) }
    }

    #[inline]
    #[verifier::external_body]
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.as_slice()
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r == string_is_ascii_spec(self),
    )]
    pub fn is_ascii(&self) -> bool {
        self.as_str().is_ascii()
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(
        ensures
            self@ == Seq::<char>::empty(),
            string_is_ascii_spec(self),
    )]
    pub fn clear(&mut self) {
        self.bytes.clear();
    }

    #[inline]
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize) {
        self.bytes.reserve(additional);
    }

    #[inline]
    #[verifier::external_body]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.bytes.reserve_exact(additional);
    }

    #[inline]
    #[verifier::external_body]
    pub fn shrink_to_fit(&mut self) {
        self.bytes.shrink_to_fit();
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(
        ensures
            self@ == old(self)@ + other@,
    )]
    pub fn push_str(&mut self, other: &str) {
        self.bytes.extend_from_slice(other.as_bytes());
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(
        ensures
            self@ == old(self)@ + seq![ch],
    )]
    pub fn push(&mut self, ch: char) {
        let mut buf = [0u8;4];
        let encoded = ch.encode_utf8(&mut buf);
        self.bytes.extend_from_slice(encoded.as_bytes());
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            match r {
                Some(ch) => {
                    &&& old(self)@.len() > 0
                    &&& ch == old(self)@[old(self)@.len() - 1]
                    &&& self@ == old(self)@.subrange(0, old(self)@.len() - 1)
                },
                None => {
                    &&& old(self)@.len() == 0
                    &&& self@ == old(self)@
                },
            },
    )]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.as_str().chars().next_back()?;
        let new_len = self.len() - ch.len_utf8();
        self.bytes.truncate(new_len);
        Some(ch)
    }
}

#[verus_verify]
impl<A: core::alloc::Allocator> core::ops::Deref for String<A> {
    type Target = str;

    #[inline]
    #[verifier::external_body]
    fn deref(&self) -> (r: &str)
        ensures
            r@ == self@,
            r.is_ascii() == string_is_ascii_spec(self),
    {
        self.as_str()
    }
}

#[verus_verify]
impl<A: core::alloc::Allocator + Clone> Clone for String<A> {
    #[inline]
    #[verifier::external_body]
    fn clone(&self) -> (r: Self)
        ensures
            r@ == self@,
            string_is_ascii_spec(&r) == string_is_ascii_spec(self),
    {
        Self { bytes: self.bytes.clone() }
    }
}

#[verus_verify]
impl<A: core::alloc::Allocator> core::cmp::PartialEq for String<A> {
    #[inline]
    #[verifier::external_body]
    fn eq(&self, other: &Self) -> (r: bool)
        ensures
            r <==> self@ == other@,
    {
        self.as_str() == other.as_str()
    }
}

#[verus_verify]
impl<A: core::alloc::Allocator> core::cmp::Eq for String<A> {

}

impl<A: core::alloc::Allocator> DekoDebug for String<A> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str(self.as_str());
    }
}

} // verus!
impl<A: core::alloc::Allocator> core::fmt::Write for String<A> {
    #[inline]
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> core::fmt::Result {
        self.push(c);
        Ok(())
    }
}
