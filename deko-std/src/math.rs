use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power2::*;
use vstd::math::*;
use vstd::prelude::*;

verus! {

pub open spec fn is_power_of_two_spec(n: u64) -> bool
    decreases n,
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else {
        is_power_of_two_spec(n / 2)
    }
}

/// Returns the next power of two greater than or equal to `n`.
pub closed spec fn next_power_of_two_spec(n: u64) -> u64
    decreases n,
{
    if n <= 1 {
        1
    } else if n == 2 {
        2
    } else if is_power_of_two_spec(n) {
        // n is already a power of two
        n
    } else {
        proof {
            assert(n > 2 ==> (n / 2 + 1) < n) by (nonlinear_arith);
        }
        let next = next_power_of_two_spec(((n / 2 + 1)) as u64);

        (next * 2) as u64
    }
}

// todo: prove this.
#[verifier::external_body]
pub proof fn lemma_next_power_of_two_then_log2_greater(a: u64, b: u64, c: u64)
    requires
        a >= b,
        c as u64 == next_power_of_two_spec(a) as u64,
    ensures
        vstd::arithmetic::logarithm::log(2, c as int) >= b,
{
}

pub assume_specification[ u64::ilog2 ](n: u64) -> (result: u32)
    requires
        n > 0,
    ensures
        result == log(2, n as int),
;

pub assume_specification[ u64::next_power_of_two ](n: u64) -> (result: u64)
    ensures
        result > 0,
        is_power_of_two_spec(result),
        result == next_power_of_two_spec(n) as u64,
;

} // verus!
