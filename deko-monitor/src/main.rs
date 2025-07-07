#![no_std]
#![no_main]

use core::arch::asm;
use core::ffi::c_void;
use core::panic::PanicInfo;

use deko_core::*;
use deko_meta::*;

// core::arch::global_asm!(include_str!("entry.S"), options(att_syntax));

/// Custom panic handler that will be called on panic.
///
/// For the time being we just enter an infinite loop.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! { loop {} }

/// This is the main entry function of the monitor and the bootstrap code should
/// eventually jump to this destination.
///
/// The bootstrap should prepare the context to satisfy `_start()`'s expectation:
/// - the memory is in 1:1 identity mapping mode with paging enabled
/// - the stack is ready for use
#[no_mangle]
pub unsafe extern "C" fn _start(header: *const Header) -> ! {
    asm!("ud2"); // for testing.

    loop {}
}
