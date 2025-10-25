#![no_std]
#![no_main]

use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("monitor.S"), options(att_syntax));

/// The "true" entry point of the monitor.
#[no_mangle]
extern "C" fn deko_entry() -> ! { loop {} }

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! { loop {} }

verus! {


} // verus!
