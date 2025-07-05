#![no_std]
#![no_main]

use uefi::prelude::*;

/// Not used.
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[entry]
fn _main() -> Status {
    uefi::helpers::init().unwrap();

    uefi::println!("Hello, UEFI World!");

    loop{}
    // Return success status.
    Status::SUCCESS
}
