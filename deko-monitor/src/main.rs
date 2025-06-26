#![no_std]
#![no_main]

use core::panic::PanicInfo;

/// Custom panic handler that will be called on panic.
/// 
/// For the time being we just enter an infinite loop.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    loop {}
}
