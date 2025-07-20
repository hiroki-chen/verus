use vstd::prelude::*;

verus! {

/// Indicates if a value if "taken" from somewhere and we do not own the permission to that.
/// By holding this token we guarantee that a value is "owned" by the caller syntactically
/// but needs to be "borrowed" semantically.
///
/// # Examples
///
/// ```rust
///     use deko_std::misc::DekoHoleToken;
///
///     // to ensure this is "borrowed" but "owned" syntactically
///     // to prevent meaningless copying and initializaing.
///     let (v, Tracked(token)) = MyArray::take(0);
/// ```
// #[verifier::external_body]
#[verifier::accept_recursive_types(V)]
pub tracked struct DekoHoleToken<'a, V> {
    id: (usize, usize),
    __marker: core::marker::PhantomData<&'a V>,
}

impl<'a, V> DekoHoleToken<'a, V> {
    #[verifier::external_body]
    pub proof fn new(parent_id: usize, id: usize) -> Self {
        Self { id: (parent_id, id), __marker: core::marker::PhantomData }
    }

    pub closed spec fn id(&self) -> (usize, usize) {
        self.id
    }
}

pub trait IsConstant {
    spec fn is_constant(&self) -> bool;
}

#[verifier::external_body]
pub proof fn lemma_is_constant_implies_constant<T: IsConstant, U: IsConstant>(
    v: T,
    f: spec_fn(T) -> U,
)
// f (c) is constant. <==> v is constant

    ensures
        v.is_constant() ==> f(v).is_constant(),
{
}

#[verifier::external_body]
pub proof fn lemma_is_constant_implies_constant_rev<T: IsConstant, U: IsConstant>(
    v: T,
    f: spec_fn(T) -> U,
)
// f (c) is constant. <==> v is constant

    ensures
        f(v).is_constant() ==> v.is_constant(),
{
}

impl<T: IsConstant> IsConstant for Option<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        match self {
            Option::None => true,
            Option::Some(t) => t.is_constant(),
        }
    }
}

impl IsConstant for () {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T1: IsConstant, T2: IsConstant> IsConstant for (T1, T2) {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        self.0.is_constant() && self.1.is_constant()
    }
}

impl<T> IsConstant for Ghost<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

impl<T> IsConstant for Tracked<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }
}

} // verus!
#[macro_export]
macro_rules! impl_spec_constant_for_basic {
    ($($type: ty),* $(,)?) => {
        $(verus!{
            impl IsConstant for $type {
                #[verifier(inline)]
                open spec fn is_constant(&self) -> bool
                {
                    true
                }

            }
        }
)*
    }
}
impl_spec_constant_for_basic! {u64, u32, u16, usize, u8, bool, char, i8, i16, i32, i64}
