#![no_std]
#![no_main]

mod kernel;

use uefi::table::system_table_raw;
use uefi::{entry, println, Status};

use crate::kernel::*;

#[entry]
unsafe fn _main() -> Status {
    uefi::helpers::init().expect("Failed to initialize UEFI helpers");

    println!("Deko Stage 1 Bootloader");
    println!("------------------------");

    let system_table = &*system_table_raw().unwrap().as_ref();

    match kernel_init(system_table) {
        Ok(kernel) => {
            // It's time to hand off control.
            println!("[+] Entering Deko kernel...");

            kernel.enter();
        }
        Err(e) => {
            panic!("Deko stage 1 failed: {}", e);
        }
    }
}
