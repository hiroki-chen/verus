#![no_std]
#![no_main]

use vstd::prelude::*;
use deko_std::prelude::*;

/// The "true" entry point of the monitor.
#[no_mangle]
extern "C" fn deko_entry() -> ! { loop {} }

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! { loop {} }

verus! {
    
}