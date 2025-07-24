use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

#[verifier::bit_vector]
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

#[verifier::bit_vector]
pub proof fn lemma_xor_is_or_minus_and()
    ensures
        forall|a: u64, b: u64| #[trigger] (a ^ b) == (a | b) - (a & b),
        forall|a: u32, b: u32| #[trigger] (a ^ b) == (a | b) - (a & b),
        forall|a: u16, b: u16| #[trigger] (a ^ b) == (a | b) - (a & b),
        forall|a: u8, b: u8| #[trigger] (a ^ b) == (a | b) - (a & b),
{
}

pub proof fn lemma_lt_is_power_of_two_bitor(p: u64, x: u64, y: u64, n: u64)
    requires
        0 <= n < 64,
        pow(2, n as nat) == p,
        x < p,
        y < p,
    ensures
        (x | y) < p,
{
    if p == 1 {
        // As per the documentation of Verus, "The prover does not have access
        // to any prior context except that which is given in the requires clause,
        // if provided. If the requires clause is provided, then the bit vector
        // solver attempts to prove Q ==> P. Verus will also check (using its
        // normal solver) that Q holds from the prior proof context."
        assert((x | y) == 0) by (bit_vector)
            requires
                x == 0 && y == 0,
        ;
    } else {
        lemma_u64_pow2_no_overflow(n as _);
        lemma_u64_shl_is_mul(1u64, n);
        lemma_pow2(n as nat);

        assert((x | y) < p) by (bit_vector)
            requires
                p == (1u64 << n) && x < p && y < p,

    }
}

} // verus!
