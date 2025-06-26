#![no_std]
#![feature(abi_x86_interrupt)]

#[cfg(target_arch="x86")]
compile_error!("Cannot be compiled against non x86_64 architecture!");

extern crate alloc;

pub mod boot;
pub mod cpu;

use vstd::prelude::*;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

fn main() {
    assert(min(10, 20) == 10);

    assert(forall |i: int, j: int | min(i, j) <= i)
}

} // verus!
