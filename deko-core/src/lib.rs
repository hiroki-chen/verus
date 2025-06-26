#![no_std]

use vstd::prelude::*;

verus! {

fn foo() {
    assert(1 == 0 + 1);
}

} // verus!
