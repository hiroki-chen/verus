use vstd::prelude::*;

verus! {

#[verifier(bit_vector)]
pub const proof fn bit64_and_auto()
    ensures
        forall|a: u64, b: u64| #[trigger] (a & b) == b & a,
        forall|a: u64, b: u64, c: u64| #[trigger] ((a & b) & c) == a & (b & c),
        forall|a: u64| #[trigger] (a & a) == a,
        forall|a: u64| #[trigger] (a & 0) == 0,
        forall|a: u64| #[trigger] (a & 0xffffffffffffffffu64) == a,
        forall|a: u64, b: u64| #[trigger] (a & b) <= b && (a & b) <= a,
        forall|a: u32, b: u32| #[trigger] (a & b) <= b,
        forall|a: u16, b: u16| #[trigger] (a & b) <= b,
        forall|a: u8, b: u8| #[trigger] (a & b) <= b,
{
}

} // verus!
