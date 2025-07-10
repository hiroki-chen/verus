#![no_std]
#![no_main]

use core::panic::PanicInfo;

use deko_meta::*;

#[cfg(all(feature = "tdx", feature = "snp"))]
compile_error!("Cannot enable both TDX and SEV features at the same time!");

#[cfg(feature = "snp")]
core::arch::global_asm!(include_str!("stage2.S"), options(att_syntax));
#[cfg(feature = "tdx")]
core::arch::global_asm!(include_str!("stage2-tdx.S"), options(att_syntax));

/// This is the main entry function of the monitor and the bootstrap code should
/// eventually jump to this destination.
///
/// The bootstrap should prepare the context to satisfy `_start()`'s expectation:
/// - the memory is in 1:1 identity mapping mode with paging enabled
/// - the stack is ready for use
#[no_mangle]
pub unsafe extern "C" fn _start(header: *const HeaderRaw) -> ! {
    // This is to avoid the compiler from being confuseed with
    // non-existing arguments for verus verification. We do not
    // want to import anything from verus in this crate.
    core::arch::asm!(
      "call {f}",
      f = in(reg) deko_core::deko_main as usize,
      options(noreturn)
    );
}

/// Custom panic handler that will be called on panic.
///
/// For the time being we just enter an infinite loop.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! { loop {} }
