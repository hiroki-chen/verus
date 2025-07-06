#![no_std]
#![no_main]

use deko_meta::*;
use uefi::table::cfg::ACPI2_GUID;
use uefi::table::system_table_raw;
use uefi::{entry, Status};
use uefi_raw::table::system::SystemTable;

/// Not used.
#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }

#[entry]
unsafe fn _main() -> Status {
    uefi::helpers::init().unwrap();
    uefi::println!("Booting Deko Stage 1...");

    let system_table = &*system_table_raw().unwrap().as_ref();
    let configuration_table_len = system_table.number_of_configuration_table_entries;
    let configuration_table =
        core::slice::from_raw_parts(system_table.configuration_table, configuration_table_len);

    let acpi = configuration_table
        .iter()
        .find(|entry| entry.vendor_guid == ACPI2_GUID)
        .expect("ACPI 2.0 table not found");

    uefi::println!("ACPI 2.0 table found at address: {:?}", acpi.vendor_table);

    // Load the deko-monitor binary from the disk.

    loop {}
    // Return success status.
    Status::SUCCESS
}
