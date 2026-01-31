//! Specifications for the hash map. We use `hashbrown` crate as the underlying implementation.
use core::hash::Hash;
use core::ops::Deref;

use deko_macros::DekoDebug;
use hashbrown::DefaultHashBuilder;
use vstd::map::Map;
use vstd::prelude::*;

use crate::std_extra::allocator::AllocatorWrapper;
use crate::wf::WellFormed;
use crate::DekoDebug;

verus! {

type HashMapInner<K, V, A> = hashbrown::HashMap<K, V, DefaultHashBuilder, AllocatorWrapper<A>>;

/// A hash map implementation with formal verification support and custom allocator support.
///
/// This is a wrapper around [`hashbrown::HashMap`] that provides formal verification
/// capabilities through Verus. The HashMap ensures memory safety and correctness
/// properties that can be statically verified.
///
/// ## Allocator Integration
///
/// The HashMap requires an [`AllocatorWrapper`] which bridges the gap between
/// Rust's allocator interface and the alloc apis hashbrown uses.
///
/// ## Usage
///
/// ```rust,ignore
/// use deko_std::std_extra::collections::HashMap;
/// use deko_std::std_extra::allocator::AllocatorWrapper;
///
/// // Create a new HashMap with a custom allocator
/// let map = HashMap::new_in(AllocatorWrapper::new(allocator));
/// ```
#[verifier::external_body]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct HashMap<K, V, A: core::alloc::Allocator>(HashMapInner<K, V, A>);

impl<K: WellFormed, V: WellFormed, A: core::alloc::Allocator> WellFormed for HashMap<K, V, A> {
    open spec fn wf(&self) -> bool {
        forall|k: K, v: V| #[trigger] self@.kv_pairs().contains((k, v)) ==> k.wf() && v.wf()
    }
}

impl<K: DekoDebug, V: DekoDebug, A: core::alloc::Allocator> DekoDebug for HashMap<K, V, A> where
    K: DekoDebug,
    V: DekoDebug,
 {
    #[verifier::external_body]
    fn deko_debug<W: crate::DekoWriter>(&self, writer: &W) {
        writer.write_str("HashMap ");
        writer.write_str("len = ");
        self.0.len().deko_debug(writer);
        writer.write_str(" {\n");
        for (key, value) in self.0.iter() {
            writer.write_str("K: ");
            key.deko_debug(writer);
            writer.write_str(", V: ");
            value.deko_debug(writer);
            writer.write_str("\n");
        }
        writer.write_str("}");
    }
}

impl<K, VV, A: core::alloc::Allocator> View for HashMap<K, VV, A> {
    type V = Map<K, VV>;

    uninterp spec fn view(&self) -> Self::V;
}

#[verus_verify]
impl<K, V, A: core::alloc::Allocator> HashMap<K, V, A> {
    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r@ =~= Map::<K, V>::empty(),
    )]
    pub fn new_in(alloc: AllocatorWrapper<A>) -> Self {
        Self(HashMapInner::new_in(alloc))
    }
}

#[verus_verify]
impl<K: Eq + Hash, V, A: core::alloc::Allocator> HashMap<K, V, A> {
    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            self@ =~= old(self)@.insert(key, value),
            r == if old(self)@.contains_key(key) {
                Some(old(self)@[key])
            } else {
                None
            },

    )]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key, value)
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            self@ =~= old(self)@.remove(*key),
            r == old(self)@.get(*key),
    )]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.0.remove(key)
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r == self@.contains_key(*key),
    )]
    pub fn contains_key(&self, key: &K) -> bool {
        self.0.contains_key(key)
    }

    #[inline]
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r == self@.len(),
    )]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

} // verus!
