//! This is the /init process binary for Deko monitor.
#![no_std]
#![no_main]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! { loop {} }

/// The "real" entry point for the init process.
#[no_mangle]
fn _start() -> u32 { 0 }
