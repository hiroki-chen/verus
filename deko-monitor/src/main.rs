#![no_std]
#![no_main]

use core::panic::PanicInfo;
use deko_core::*;

core::arch::global_asm!(include_str!("entry.S"), options(att_syntax));


/// Custom panic handler that will be called on panic.
///
/// For the time being we just enter an infinite loop.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! { loop {} }
