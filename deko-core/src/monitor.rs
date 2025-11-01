#![no_std]
#![no_main]

use deko_core::cpu::gdt::GLOBAL_GDT;
use deko_core::mm::paging::GLOBAL;
use deko_std::prelude::*;
use vstd::prelude::*;

core::arch::global_asm!(include_str!("monitor.S"), options(att_syntax));

/// The "true" entry point of the monitor.
#[no_mangle]
extern "C" fn deko_entry() -> ! {
    GLOBAL_GDT.load_selectors();
    loop {}
}

verus! {

#[verifier::external]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {
    }
}

} // verus!
