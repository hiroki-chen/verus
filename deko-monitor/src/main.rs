#![no_std]
#![no_main]

use core::ffi::c_void;
use core::panic::PanicInfo;

use deko_core::*;

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
#[cfg_attr(target_os = "uefi", export_name = "efi_main")]
pub extern "win64" fn _start(
    boot_fv: *const c_void,
    top_of_stack: *const c_void,
    init_vp: *const c_void,
    info: usize,
) -> ! {
    loop {}
}
