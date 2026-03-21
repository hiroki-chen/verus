/// The current version.
pub const DEKO_SM_VERSION: u64 = 0x1145141919510;

/// The boot header structure used to pass information to the module at boot time.
///
/// This is a simpler version adapted from
///     https://github.com/hiroki-chen/NeoOS/tree/main/boot_header/src/lib.rs
#[repr(C)]
pub struct BootHeader {
    /// The version of the boot protocol.
    pub magic: u64,
    /// The address of the Root System Description Pointer used in the ACPI programming interface.
    pub acpi2_rsdp_addr: u64,
    /// The kernel entry.
    pub kernel_entry: u64,
    /// The boot argument of the Linux kernel.
    pub kernel_boot_arg: [u8; 8192],
    /// The size of the boot argument.
    pub kernel_boot_arg_size: u32,
    /// The header to the linux bootloader.
    ///
    /// TODO: This is a placeholder for the actual linux boot header.
    pub linux_boot_header: (),
    /// The size of the linux boot header.
    pub linux_boot_header_size: u64,
}
