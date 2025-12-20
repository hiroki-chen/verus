use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::math::*;
use vstd::prelude::*;

verus! {

#[verifier::inline]
pub open spec fn is_power_of_two_spec(n: nat) -> bool {
    exists|exp: nat| n == #[trigger] pow(2, exp)
}

#[verifier::inline]
pub open spec fn is_power_of_two(n: u64) -> bool {
    n > 0 && (n & (n - 1) as u64) == 0
}

/// Proof that the two definitions of "is power of two" are equivalent.
///
/// The key reason why we have two different definitions is that the
/// bitwise definition is more convenient to use in code, while the
/// mathematical definition is more convenient to reason about so
/// one can easily construct a "witness" exponent.
///
/// This proof establishes the connection between the two definitions in case
/// there might be deifferent usages to state the same fact.
pub proof fn lemma_is_power_of_two_equiv(n: u64)
    ensures
        is_power_of_two(n) <==> is_power_of_two_spec(n as nat),
    decreases n,
{
    // Using broadcast proofs from vstd
    // somehow makes the proof body less
    // straightforward so we just import
    // what we need in the proof body.
    if n == 0 {
        assert(!is_power_of_two(n));
        assert(!is_power_of_two_spec(n as nat)) by {
            assert forall|exp: nat| pow(2, exp) > 0 by {
                lemma_pow2_pos(exp);
                lemma_pow2(exp);
            }
        }
    }
    if n == 1 {
        assert(1 & 0 == 0) by (bit_vector);
        assert(is_power_of_two_spec(n as nat)) by {
            lemma2_to64();
            assert(1 == pow2(0));
            lemma_pow2(0);
        }
    } else {
        if is_power_of_two_spec(n as nat) {
            assert(n >= 2);
            let exp = choose|exp: nat| n as nat == pow(2, exp);
            assert(exp >= 1) by {
                lemma2_to64();
                lemma_pow2(1);
                lemma_pow_increases_converse(2, 1, exp);
            }

            lemma_pow2(exp);
            lemma_pow2((exp - 1) as nat);
            lemma_pow2_unfold(exp);
            assert(n as nat == 2 * pow2((exp - 1) as nat));
            assert(n % 2 == 0);
            assert(n >> 1 == pow2((exp - 1) as nat)) by {
                lemma2_to64();
                lemma_pow2(1);
                lemma_u64_shr_is_div(n, 1);
            }
            lemma_is_power_of_two_equiv(pow2((exp - 1) as nat) as u64);  // induction case.

            assert((n & (n - 1) as u64) == 0) by (bit_vector)
                requires
                    (n >> 1) & ((n >> 1) - 1) as u64 == 0,
                    (n >> 1) > 0,
                    n % 2 == 0,
            ;
        }
        if is_power_of_two(n) {
            assert(n >= 2);
            assert(n & (n - 1) as u64 == 0);

            assert(((n >> 1) & ((n >> 1) - 1) as u64) == 0) by (bit_vector)
                requires
                    n > 1,
                    (n & (n - 1) as u64) == 0,
            ;
            assert((n >> 1) > 0) by (bit_vector)
                requires
                    n >= 2,
            ;

            assert(n >> 1 < n) by (bit_vector)
                requires
                    n > 1,
            ;  // for termination measure
            lemma_is_power_of_two_equiv((n >> 1) as u64);  // also induction case.
            assert(is_power_of_two_spec((n >> 1) as nat));

            let exp_minus_1 = choose|e: nat| (n >> 1) as nat == pow(2, e);
            lemma_pow2(exp_minus_1);
            lemma_pow2((exp_minus_1 + 1) as nat);
            lemma_pow2_unfold((exp_minus_1 + 1) as nat);

            // LATER: Need some oveflow checking but should be easy here.
            assert(n as nat == 2 * pow2(exp_minus_1)) by {
                admit();
            }
        }
    }
}

pub open spec fn next_power_of_two_spec(n: nat) -> nat {
    if n == 0 || n == 1 {
        1
    } else {
        let exp = log(2, n as int) as nat;
        if pow(2, exp) == n {
            pow(2, exp) as nat
        } else {
            pow(2, exp + 1) as nat
        }
    }
}

#[verifier::inline]
/// Returns the next power of two greater than or equal to `n`.
pub open spec fn next_power_of_two_correct(n: nat, res: nat) -> bool {
    exists|e: nat|
        if n == #[trigger] pow(2, e) {
            res == n
        } else {
            res == pow(2, e + 1) && pow(2, e) < n < res
        }
}

pub assume_specification[ u64::ilog2 ](n: u64) -> (result: u32)
    requires
        n > 0,
    ensures
        result == log(2, n as int),
;

pub assume_specification[ usize::ilog2 ](n: usize) -> (result: u32)
    requires
        n > 0,
    ensures
        result == log(2, n as int),
;

pub assume_specification[ u64::next_power_of_two ](n: u64) -> (result: u64)
    ensures
        result == next_power_of_two_spec(n as nat),
        next_power_of_two_correct(n as nat, result as nat),
;

pub assume_specification[ usize::next_power_of_two ](n: usize) -> (result: usize)
    ensures
        result == next_power_of_two_spec(n as nat),
        next_power_of_two_correct(n as nat, result as nat),
;

pub assume_specification[ u64::pow ](n: u64, exp: u32) -> (result: u64)
    ensures
        result == vstd::arithmetic::power::pow(n as int, exp as nat),
;

} // verus!
