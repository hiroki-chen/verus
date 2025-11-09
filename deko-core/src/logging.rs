//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
//!
//! TODO: Overhaul this module to fit both snp and tdx.
use core::fmt::Write;

use deko_std::prelude::*;
#[cfg(feature = "logging")]
use lexical_core::{write_with_options, NumberFormatBuilder, WriteIntegerOptions};
use vstd::prelude::*;

use crate::hal::{PlatformType, PLATFORM};
use crate::snp::logging::GHCB_IO_PORT;

#[cfg(feature = "logging")]
mod warning {
    #![deprecated = "
        Logging is an unverified feature and should not be enabled in production code.
        It is only used for debugging purposes.
    "]
}

verus! {

pub const RESET_COLOR: &'static str = "\x1B[0m";

pub const ERROR_COLOR: &'static str = "\x1B[31m";

// Red
pub const WARN_COLOR: &'static str = "\x1B[33m";

// Yellow
pub const INFO_COLOR: &'static str = "\x1B[32m";

// Green
pub const DEBUG_COLOR: &'static str = "\x1B[34m";

// Blue
pub const TRACE_COLOR: &'static str = "\x1B[36m";

// Build information constants - populated by build.rs
pub const GIT_HASH: &'static str = env!("DEKO_GIT_HASH");
pub const BUILD_TIME: &'static str = env!("DEKO_BUILD_TIME");

// ASCII Art Banner
pub const DEKO_BANNER: &'static str = r#"

██████╗ ███████╗██╗  ██╗ ██████╗ 
██╔══██╗██╔════╝██║ ██╔╝██╔═══██╗
██║  ██║█████╗  █████╔╝ ██║   ██║
██║  ██║██╔══╝  ██╔═██╗ ██║   ██║
██████╔╝███████╗██║  ██╗╚██████╔╝
╚═════╝ ╚══════╝╚═╝  ╚═╝ ╚═════╝ 

"#;

/// Using a dynamic trait object is not supported by verus, so this
/// is just
pub struct Console;

exec static CONSOLE: RwLockNoPred<Console>
    ensures
        CONSOLE.wf(),
{
    let lock = RwLockNoPred::new(Console {  }, Ghost(TrivialPredicate::new()));
    proof {
        use_type_invariant(&lock);
    }

    lock
}

impl WellFormed for Console {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl Console {
    #[verifier::external_body]
    fn write_bytes(&self, buffer: &[u8]) {
        let platform_type = match PLATFORM.get() {
            Some(p) => p,
            None => return ,
        };

        for b in buffer.iter() {
            // dispatch to platform-specific implementation
            match platform_type {
                PlatformType::Snp => {
                    let ghcb_port = match GHCB_IO_PORT.get() {
                        Some(p) => p,
                        None => return ,
                    };

                    ghcb_port.outb(*b);
                },
                _ => {
                    // Unsupported platform; do nothing
                },
            }
        }
    }
}

#[verifier::external]
impl core::fmt::Write for Console {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.write_bytes(s.as_bytes());
        Ok(())
    }
}

} // verus!
#[cfg(feature = "logging")]
verus! {

macro_rules! debug_packed_field {
    ($self:expr, $field:ident, $method:ident) => {
        let value = $self.$field;
        value.$method();
    };
}

#[verifier::external_body]
fn print_byte_hex_padded(byte: u8) {
    let hex_chars = b"0123456789ABCDEF";
    print_char(hex_chars[(byte >> 4) as usize] as char);
    print_char(hex_chars[(byte & 0xF) as usize] as char);
}

#[verifier::external_body]
pub(crate) fn print_str(s: &str) {
    let (mut console, write_handle) = CONSOLE.acquire_write();
    console.write_str(s).unwrap();
    write_handle.release_write(console);
}

#[verifier::external_body]
pub(crate) fn print_char(c: char) {
    let mut buffer = [0u8; 4];
    let s = c.encode_utf8(&mut buffer);
    print_str(s);
}

#[verifier::external_body]
pub(crate) fn print_bytes(bytes: &[u8]) {
    let (mut console, write_handle) = CONSOLE.acquire_write();
    console.write_bytes(bytes);
    write_handle.release_write(console);
}

// Specific helpers for common cases with optimized buffer sizes
#[verifier::external_body]
pub(crate) fn print_integer_hex<T: lexical_core::ToLexicalWithOptions>(num: T) {
    print_str("0x");

    const FORMAT: u128 = NumberFormatBuilder::hexadecimal();
    let mut buffer = [0u8; 32]; // Enough for 128-bit hex
    let digits = write_with_options::<_, { FORMAT }>(
        num,
        &mut buffer,
        &T::Options::default(),
    );

    print_bytes(&digits);
}

#[verifier::external_body]
pub(crate) fn print_integer_oct<T: lexical_core::ToLexicalWithOptions>(num: T) {
    print_str("0o");
    
    const FORMAT: u128 = NumberFormatBuilder::octal();
    let mut buffer = [0u8; 44]; // Enough for 128-bit octal
    let digits = write_with_options::<_, { FORMAT }>(
        num,
        &mut buffer,
        &T::Options::default(),
    );

    print_bytes(&digits);
}

#[verifier::external_body]
pub(crate) fn print_integer_bin<T: lexical_core::ToLexicalWithOptions>(num: T) {
    print_str("0b");
    const FORMAT: u128 = NumberFormatBuilder::binary();
    let mut buffer = [0u8; 128]; // Enough for 128-bit
    let digits = write_with_options::<_, { FORMAT }>(
        num,
        &mut buffer,
        &T::Options::default(),
    );

    print_bytes(&digits);
}

// Enhanced byte formatting using lexical
#[verifier::external_body]
pub(crate) fn print_byte_hex(byte: u8) {
    let mut buffer = [0u8; 2];

    const FORMAT: u128 = NumberFormatBuilder::hexadecimal();
    let digits = write_with_options::<_, { FORMAT }>(
        byte,
        &mut buffer,
        &Default::default(),
    );

    print_bytes(&digits);
}

#[verifier::external_body]
pub(crate) fn print_offset_hex(offset: usize) {
    let mut buffer = [0u8; 16]; // Enough for 64-bit hex

    const FORMAT: u128 = NumberFormatBuilder::hexadecimal();
    let digits = write_with_options::<_, { FORMAT }>(
        offset,
        &mut buffer,
        &Default::default(),
    );

    print_bytes(&digits);
}

#[verifier::external_body]
pub(crate) fn print_hex_dump_readable(bytes: &[u8], start_offset: usize) {
    if bytes.is_empty() {
        print_str("(empty)\n");
        return;
    }

    const BYTES_PER_LINE: usize = 16;

    // Print header
    print_str("       00 01 02 03 04 05 06 07  08 09 0A 0B 0C 0D 0E 0F  |ASCII          |\n");
    print_str("       ────────────────────────────────────────────────  ──────────────────\n");

    for (line_idx, chunk) in bytes.chunks(BYTES_PER_LINE).enumerate() {
        let offset = start_offset + (line_idx * BYTES_PER_LINE);

        // Print offset with consistent width
        print_offset_padded(offset);
        print_str(" │ ");

        // Print hex bytes in two groups of 8
        for (i, &byte) in chunk.iter().enumerate() {
            if i == 8 {
                print_str(" "); // Extra space between groups
            }
            print_byte_hex_padded(byte);
            print_str(" ");
        }

        // Pad incomplete lines
        let padding_needed = BYTES_PER_LINE - chunk.len();
        for i in 0..padding_needed {
            if chunk.len() + i == 8 {
                print_str(" "); // Maintain group spacing
            }
            print_str("   "); // 3 spaces (2 hex + 1 space)
        }

        print_str(" │");

        // Print ASCII with visual clarity
        for &byte in chunk.iter() {
            let c = match byte {
                0x00..=0x1F => '·',           // Control chars as middle dot
                0x20..=0x7E => byte as char,   // Printable ASCII
                0x7F => '⌂',                  // DEL as house symbol
                0x80..=0xFF => '▒',           // Extended ASCII as block
            };
            print_char(c);
        }

        // Pad ASCII section for incomplete lines
        for _ in 0..padding_needed {
            print_char(' ');
        }

        print_str("│\n");
    }

    // Print footer
    print_str("       ────────────────────────────────────────────────  ──────────────────\n");
}

#[verifier::external_body]
fn print_offset_padded(offset: usize) {
    // Print 6-digit hex offset with leading zeros
    let mut buffer = [b'0'; 6];
    let mut temp = offset;
    let hex_chars = b"0123456789ABCDEF";

    for i in (0..6).rev() {
        buffer[i] = hex_chars[temp & 0xF];
        temp >>= 4;
    }

    for &b in buffer.iter() {
        print_char(b as char);
    }
}

/// Print the Deko kernel banner with build information
#[verifier::external_body]
pub fn print_banner() {
    // Print the ASCII banner
    print_str(DEKO_BANNER);

    // Print build information
    print_str("Deko Secure Monitor - Verified System Monitor\n");
    print_str("Built on: ");
    print_str(BUILD_TIME);
    print_str("\n");
    print_str("Git commit: ");
    print_str(GIT_HASH);
    print_str("\n");
    print_str("Repository: https://github.com/hiroki-chen/cage-sev\n");
    print_str("\n");
}

/// Print panic information with detailed context.
///
/// Calling [`vstd::vpanic`] will force on-heap allocation for [`core::string::String`] which
/// is not suitable for us and thus the panic information will be instead overriden by the
/// the global allocator since we explicitly disabled global allocator in Rust.
///
/// Thus the workaround for printing panic information is to implement another stack unwinder
/// to extract information that excludes the allocation error.
#[verifier::external]
pub fn print_panic_info(info: &core::panic::PanicInfo) {
    print_str("\n");
    print_str(ERROR_COLOR);
    print_str("=== KERNEL PANIC ===\n");
    print_str(RESET_COLOR);

    // Print build information for debugging
    print_str("Build: ");
    print_str(GIT_HASH);
    print_str(" (");
    print_str(BUILD_TIME);
    print_str(")\n");

    // Print panic message if available
    if let Some(message) = info.message().as_str() {
        print_str("Message: ");
        print_str(message);
        print_str("\n");
    } else {
        print_str("Message: <no message>\n");
    }

    // Print panic location if available
    if let Some(location) = info.location() {
        print_str("Location: ");
        location.file().deko_debug();
        print_str(":");
        location.line().deko_debug();
        print_str(":");
        location.column().deko_debug();
        print_str("\n");
    } else {
        print_str("Location: <unknown>\n");
    }

    // Print payload information
    let payload = info.payload();
    if let Some(s) = payload.downcast_ref::<&str>() {
        print_str("Payload: \"");
        print_str(s);
        print_str("\"\n");
    } else {
        print_str("Payload: <non-string>\n");
    }

    print_str("\n");
    print_str(ERROR_COLOR);
    print_str("=== SYSTEM HALTED ===\n");
    print_str(RESET_COLOR);
}

/// Custom debug trait for Verus-compatible debugging without heap allocation
pub trait DekoDebug {
    /// Print debug information for this type
    fn deko_debug(&self);

    fn deko_debug_hex(&self) {
        print_str("No hex debug format available");
    }

    fn deko_debug_oct(&self) {
        print_str("No octal debug format available");
    }
}

// Remove the generic implementation and use a macro instead
macro_rules! impl_deko_debug_integer {
    ($($ty:ty),* $(,)?) => {
        $(
            verus! {
                
            impl DekoDebug for $ty {
                #[verifier::external_body]
                fn deko_debug(&self) {
                    let mut buffer = itoa::Buffer::new();
                    let s = buffer.format(*self);
                    print_str(s);
                }

                #[verifier::external_body]
                fn deko_debug_hex(&self) {
                    print_integer_hex(*self);
                }

                #[verifier::external_body]
                fn deko_debug_oct(&self) {
                    print_integer_oct(*self);
                }
            }
            }
        )*
    };
}

// Implement for all integer types explicitly
impl_deko_debug_integer!(
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
);


impl DekoDebug for bool {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str(if *self { "true" } else { "false" });
    }
}

impl DekoDebug for char {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_char(*self);
    }
}

impl DekoDebug for &str {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str(self);
    }
}

impl<T> DekoDebug for *const T {
    #[verifier::external_body]
    fn deko_debug(&self) {
        (*self as usize).deko_debug();
    }
}

impl<T> DekoDebug for *mut T {
    #[verifier::external_body]
    fn deko_debug(&self) {
        (*self as usize).deko_debug();
    }
}

impl<T: DekoDebug> DekoDebug for Option<T> {
    #[verifier::external_body]
    fn deko_debug(&self) {
        match self {
            Some(ref inner) => {
                print_str("Some(");
                inner.deko_debug();
                print_char(')');
            }
            None => print_str("None"),
        }
    }
}

impl<T: DekoDebug, E: DekoDebug> DekoDebug for Result<T, E> {
    #[verifier::external_body]
    fn deko_debug(&self) {
        match self {
            Ok(ref inner) => {
                print_str("Ok(");
                inner.deko_debug();
                print_char(')');
            }
            Err(ref inner) => {
                print_str("Err(");
                inner.deko_debug();
                print_char(')');
            }
        }
    }
}

impl<'a> DekoDebug for &'a [u8] {
    #[verifier::external_body]
    fn deko_debug(&self) {
        if self.is_empty() {
            print_str("&[u8] { len: 0, data: [] }");
            return;
        }

        match self.len() {
            1..=8 => {
                // Very short - inline with brackets
                print_str("&[u8] { len: ");
                self.len().deko_debug();
                print_str(", data: [");
                for (i, &byte) in self.iter().enumerate() {
                    if i > 0 { print_str(", "); }
                    print_str("0x");
                    print_byte_hex_padded(byte);
                }
                print_str("] }");
            }
            9..=32 => {
                // Short - compact hex line
                print_str("&[u8] { len: ");
                self.len().deko_debug();
                print_str(", data:\n  ");

                for (i, &byte) in self.iter().enumerate() {
                    if i > 0 && i % 8 == 0 {
                        print_str("\n  ");
                    } else if i > 0 {
                        print_str(" ");
                    }

                    print_str("0x");
                    print_byte_hex_padded(byte);
                }
                print_str("\n}");
            }
            _ => {
                // Long - full hex dump
                print_str("&[u8] { len: ");
                self.len().deko_debug();
                print_str(", data:\n");
                print_hex_dump_readable(self, 0);
                print_str("}");
            }
        }
    }
}
impl DekoDebug for deko_std::boot::IgvmParamBlock {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("IgvmParamBlock {\n");

        print_str("  param_area_size: ");
        debug_packed_field!(self, param_area_size, deko_debug);
        print_str(",\n");

        print_str("  debug_serial_port: ");
        debug_packed_field!(self, debug_serial_port, deko_debug_hex);
        print_str(",\n");

        print_str("  use_alternate_injection: ");
        let use_alternate_injection = self.use_alternate_injection;
        (use_alternate_injection != 0).deko_debug();
        print_str(",\n");

        print_str("  vtom: ");
        debug_packed_field!(self, vtom, deko_debug_hex);
        print_str(",\n");

        print_str("  kernel_base: ");
        debug_packed_field!(self, kernel_base, deko_debug_hex);
        print_str(",\n");

        print_str("  kernel_min_size: ");
        debug_packed_field!(self, kernel_min_size, deko_debug);
        print_str(",\n");

        print_str("  kernel_max_size: ");
        debug_packed_field!(self, kernel_max_size, deko_debug);
        print_str(",\n");

        print_str("  stage1_size: ");
        debug_packed_field!(self, stage1_size, deko_debug);
        print_str(",\n");

        print_str("  stage1_base: ");
        debug_packed_field!(self, stage1_base, deko_debug_hex);
        print_str(",\n");

        print_str("  firmware: ");
        debug_packed_field!(self, firmware, deko_debug);
        print_str(",\n");

        print_char('}');
    }
}

impl DekoDebug for deko_std::boot::IgvmParamBlockFwInfo {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("IgvmParamBlockFwInfo {\n");

        print_str("    start: ");
        debug_packed_field!(self, start, deko_debug_hex);
        print_str(",\n");

        print_str("    size: ");
        debug_packed_field!(self, size, deko_debug);
        print_str(",\n");

        print_str("    in_low_memory: ");
        (self.in_low_memory != 0).deko_debug();
        print_str(",\n");

        print_str("    secrets_page: ");
        debug_packed_field!(self, secrets_page, deko_debug_hex);
        print_str(",\n");

        print_str("    cpuid_page: ");
        debug_packed_field!(self, cpuid_page, deko_debug_hex);
        print_str(",\n");

        print_str("    prevalidated_count: ");
        debug_packed_field!(self, prevalidated_count, deko_debug);
        print_str(",\n");

        print_str("    prevalidated: [");
        for i in 0..8 {
            if i < self.prevalidated_count {
                if i > 0 {
                    print_str(", ");
                }
                // Access array element safely
                self.prevalidated.0[i as usize].deko_debug();
            }
        }
        print_str("]\n");

        print_str("  }");
    }
}

impl DekoDebug for deko_std::boot::IgvmParamBlockFwMem {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("{ base: ");
        debug_packed_field!(self, base, deko_debug_hex);
        print_str(", size: ");
        debug_packed_field!(self, size, deko_debug);
        print_str(" }");
    }
}

// DekoDebug implementations for DekoCtx and related types
impl DekoDebug for crate::cpu::ctx::DekoCtx {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("DekoCtx {\n");

        print_str("  stage2_launch_info: ");
        (self.stage2_launch_info.addr() as usize).deko_debug_hex();
        print_str(",\n");

        print_str("  pgtable: ");
        (self.pgtable.addr() as usize).deko_debug_hex();
        print_str(",\n");

        print_str("  gdt: ");
        (self.gdt.addr() as usize).deko_debug_hex();
        print_str(",\n");

        print_str("  mapping_space: ");
        self.mapping_space.deko_debug();
        print_str(",\n");

        print_char('}');
    }
}

// DekoDebug implementation for MappingSpace from deko-std
impl DekoDebug for deko_std::address::MappingSpace {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("MappingSpace {\n");

        print_str("    kernel: ");
        self.kernel.deko_debug();
        print_str(",\n");

        print_str("    physmap: ");
        self.physmap.deko_debug();
        print_str(",\n");

        print_str("  }");
    }
}

// DekoDebug implementation for FixedAddressMappingRange from deko-std
impl DekoDebug for deko_std::address::FixedAddressMappingRange {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("FixedAddressMappingRange {\n");

        print_str("      virt_start: ");
        self.virt_start.0.deko_debug_hex();
        print_str(",\n");

        print_str("      virt_end: ");
        self.virt_end.0.deko_debug_hex();
        print_str(",\n");

        print_str("      phys_start: ");
        self.phys_start.0.deko_debug_hex();
        print_str(",\n");

        print_str("    }");
    }
}

macro_rules! print_with_format {
    ($expr:expr => hex) => {
        {
            use $crate::logging::DekoDebug;
            $expr.deko_debug_hex();
        }
    };
    ($expr:expr => oct) => {
        {
            use $crate::logging::DekoDebug;
            $expr.deko_debug_oct();
        }
    };
    ($expr:expr => dec) => {
        {
            use $crate::logging::DekoDebug;
            $expr.deko_debug();
        }
    };

    // Custom radix support
    ($expr:expr => base($radix:literal)) => {
        $crate::logging::print_integer_lexical_base($expr, $radix);
    };

    // Boolean with custom text
    ($expr:expr => enabled) => {
        $crate::logging::print_str(if $expr { "enabled" } else { "disabled" });
    };
    ($expr:expr => yesno) => {
        $crate::logging::print_str(if $expr { "yes" } else { "no" });
    };
    ($expr:expr => onoff) => {
        $crate::logging::print_str(if $expr { "on" } else { "off" });
    };

    // Default formatting (no specifier)
    ($expr:expr) => {
        {
            use $crate::logging::DekoDebug;
            $expr.deko_debug();
        }
    };
}

// Internal macro for variadic argument processing
macro_rules! print_args_internal {
    // Base case - no arguments
    () => {};

    // Single argument with format specifier
    ($arg:expr => $fmt:ident) => {
        $crate::logging::print_with_format!($arg => $fmt);
    };
    ($arg:expr => $fmt:ident($param:literal)) => {
        $crate::logging::print_with_format!($arg => $fmt($param));
    };

    // Single argument without format specifier
    ($arg:expr) => {
        $crate::logging::print_with_format!($arg);
    };

    // Multiple arguments - first with format specifier
    ($head:expr => $fmt:ident, $($tail:tt)*) => {
        $crate::logging::print_with_format!($head => $fmt);
        $crate::logging::print_str(" ");
        $crate::logging::print_args_internal!($($tail)*);
    };
    ($head:expr => $fmt:ident($param:literal), $($tail:tt)*) => {
        $crate::logging::print_with_format!($head => $fmt($param));
        $crate::logging::print_str(" ");
        $crate::logging::print_args_internal!($($tail)*);
    };

    // Multiple arguments - first without format specifier
    ($head:expr, $($tail:tt)*) => {
        $crate::logging::print_with_format!($head);
        $crate::logging::print_str(" ");
        $crate::logging::print_args_internal!($($tail)*);
    };
}

} // verus!


// Should be defined outside verus! block to allow macro export
// otherwise the macro hygiene will complain about $crate usage.
#[macro_export]
macro_rules! kinfo {
    ($($args:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $crate::logging::print_str($crate::logging::INFO_COLOR);
            $crate::logging::print_str("[INFO] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");
        }
    };
}

#[macro_export]
macro_rules! kwarn {
    ($($args:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $crate::logging::print_str($crate::logging::WARN_COLOR);
            $crate::logging::print_str("[WARN] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");
        }
    };
}

#[macro_export]
macro_rules! kerror {
    ($($args:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $crate::logging::print_str($crate::logging::ERROR_COLOR);
            $crate::logging::print_str("[ERROR] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");
        }
    };
}

#[macro_export]
macro_rules! kdebug {
    ($($args:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $crate::logging::print_str($crate::logging::DEBUG_COLOR);
            $crate::logging::print_str("[DEBUG] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");
        }
    };
}

#[macro_export]
macro_rules! ktrace {
    ($($args:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $crate::logging::print_str($crate::logging::TRACE_COLOR);
            $crate::logging::print_str("[TRACE] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");
        }
    };
}

pub(crate) use {
    print_args_internal,
    print_with_format,
};
