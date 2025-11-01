//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
//!
//! TODO: Overhaul this module to fit both snp and tdx.
use core::fmt::Write;

use deko_std::prelude::*;
use lexical_write_integer::Options;
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

#[verifier::external]
impl log::Log for Console {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        if self.enabled(record.metadata()) {
            return ;
        }
        match record.metadata().level() {
            log::Level::Error => __print(
                format_args!(
                    "{}[Deko-Monitor] {}: {}{}\n",
                    ERROR_COLOR,
                    record.metadata().level().as_str(),
                    record.args(),
                    RESET_COLOR
                ),
            ),
            log::Level::Warn => __print(
                format_args!(
                    "{}[Deko-Monitor] {}: {}{}\n",
                    WARN_COLOR,
                    record.metadata().level().as_str(),
                    record.args(),
                    RESET_COLOR
                ),
            ),
            log::Level::Info => __print(
                format_args!(
                    "{}[Deko-Monitor] {}: {}{}\n",
                    INFO_COLOR,
                    record.metadata().level().as_str(),
                    record.args(),
                    RESET_COLOR
                ),
            ),
            log::Level::Debug => __print(
                format_args!(
                    "{}[Deko-Monitor] {}: {}{}\n",
                    DEBUG_COLOR,
                    record.metadata().level().as_str(),
                    record.args(),
                    RESET_COLOR
                ),
            ),
            log::Level::Trace => __print(
                format_args!(
                    "{}[Deko-Monitor] {}: {}{}\n",
                    TRACE_COLOR,
                    record.metadata().level().as_str(),
                    record.args(),
                    RESET_COLOR
                ),
            ),
        }
    }

    fn flush(&self) {
    }
}

#[verifier::external]
pub(crate) fn __print(arg: core::fmt::Arguments) {
    let (mut console, write_handle) = CONSOLE.acquire_write();
    console.write_fmt(arg).unwrap();
    write_handle.release_write(console);
}

#[verifier::external]
pub(crate) fn __print_str(s: &str) {
    let (mut console, write_handle) = CONSOLE.acquire_write();
    console.write_str(s).unwrap();
    write_handle.release_write(console);
}

#[verifier::external_body]
pub(crate) fn __hex<'a, T>(num: T)
where
   T: lexical_write_integer::ToLexicalWithOptions<Options = lexical_write_integer::Options>,
{
    let mut buffer = [0u8; 18];
    buffer[0] = b'0';
    buffer[1] = b'x';
    // Use lexical with base-16 formatting
    use lexical_write_integer::{ToLexicalWithOptions, NumberFormatBuilder};
    let options = lexical_write_integer::Options::new();
    const FORMAT: u128 = NumberFormatBuilder::from_radix(16);

    let digits = num.to_lexical_with_options::<FORMAT>(&mut buffer[2..], &options);
    let len = digits.len() + 2; // +2 for "0x"
    let s = core::str::from_utf8(&buffer[..len]).unwrap_or("<hex-error>");

    __print_str(s);
}

} // verus!
#[cfg(feature = "logging")]
verus! {

/// Print integer in decimal format using itoa for maximum efficiency
#[verifier::external_body]
pub fn print_integer<T: itoa::Integer>(num: T) {
    let mut buffer = itoa::Buffer::new();
    let s = buffer.format(num);
    print_str(s);
}

/// Print integer in hexadecimal format using optimized conversion
#[verifier::external_body]
pub fn print_integer_hex<T>(num: T)
where
    T: core::fmt::LowerHex,
{
    __print(format_args!("{:x}", num));
}

/// Print integer in hexadecimal format with 0x prefix
#[verifier::external_body]
pub fn print_integer_hex_prefixed<T>(num: T)
where
    T: core::fmt::LowerHex,
{
    __print(format_args!("0x{:x}", num));
}

/// Print float in decimal format using ryu for maximum efficiency
#[verifier::external_body]
pub fn print_float_decimal(num: f64) {
    let mut buffer = ryu::Buffer::new();
    let s = buffer.format(num);
    print_str(s);
}

/// Print float in scientific notation using core formatting
#[verifier::external_body]
pub fn print_float_scientific(num: f64) {
    __print(format_args!("{:e}", num));
}

/// Print 32-bit float in decimal format using ryu
#[verifier::external_body]
pub fn print_f32_decimal(num: f32) {
    let mut buffer = ryu::Buffer::new();
    let s = buffer.format(num);
    print_str(s);
}

/// Print unsigned integer in decimal format using core formatting
#[verifier::external_body]
pub fn print_uint_decimal<T>(num: T)
where
    T: core::fmt::Display,
{
    __print(format_args!("{}", num));
}

/// Print signed integer in decimal format using core formatting
#[verifier::external_body]
pub fn print_int_decimal<T>(num: T)
where
    T: core::fmt::Display,
{
    __print(format_args!("{}", num));
}

/// Print unsigned integer with custom base (2-36) using manual conversion
#[verifier::external_body]
pub fn print_uint_base<T>(num: T, base: u8)
where
    T: Into<u64> + Copy,
{
    if base < 2 || base > 36 {
        __print(format_args!("<invalid_base>"));
        return;
    }

    let mut num: u64 = num.into();
    if num == 0 {
        __print(format_args!("0"));
        return;
    }

    let mut buffer = [0u8; 64]; // 64 bits max
    let mut i = 0;

    while num > 0 {
        let digit = (num % base as u64) as u8;
        buffer[i] = if digit < 10 {
            b'0' + digit
        } else {
            b'a' + digit - 10
        };
        num /= base as u64;
        i += 1;
    }

    // Reverse the buffer since we built it backwards
    buffer[..i].reverse();

    // Convert to string and print
    if let Ok(s) = core::str::from_utf8(&buffer[..i]) {
        __print(format_args!("{}", s));
    } else {
        __print(format_args!("<base_error>"));
    }
}

/// Print integer in binary format
#[verifier::external_body]
pub fn print_integer_binary<T>(num: T)
where
    T: core::fmt::Binary,
{
    __print(format_args!("{:b}", num));
}

/// Print integer in octal format
#[verifier::external_body]
pub fn print_integer_octal<T>(num: T)
where
    T: core::fmt::Octal,
{
    __print(format_args!("{:o}", num));
}

/// Print bytes as hexadecimal dump
#[verifier::external_body]
pub fn print_hex_dump(data: &[u8], bytes_per_line: usize) {
    for (i, chunk) in data.chunks(bytes_per_line).enumerate() {
        // Print offset
        __print(format_args!("{:04x}: ", i * bytes_per_line));

        // Print hex values
        for &byte in chunk {
            __print(format_args!("{:02x} ", byte));
        }

        // Pad if necessary
        for _ in chunk.len()..bytes_per_line {
            __print(format_args!("   "));
        }

        // Print ASCII representation
        __print(format_args!("| "));
        for &byte in chunk {
            if byte.is_ascii_graphic() {
                __print(format_args!("{}", byte as char));
            } else {
                __print(format_args!("."));
            }
        }

        __print(format_args!("\n"));
    }
}

/// Print memory address in standard format
#[verifier::external_body]
pub fn print_address<T>(ptr: *const T) {
    __print(format_args!("{:p}", ptr));
}

/// Print raw string without any formatting
#[verifier::external_body]
#[inline]
pub fn print_str(out: &str) {
    __print(format_args!("{}", out));
}

/// Print string with newline
#[verifier::external_body]
#[inline]
pub fn print_str_ln(out: &str) {
    __print(format_args!("{}\n", out));
}

/// Print character
#[verifier::external_body]
#[inline]
pub fn print_char(c: char) {
    __print(format_args!("{}", c));
}

/// Print boolean value
#[verifier::external_body]
#[inline]
pub fn print_bool(b: bool) {
    __print(format_args!("{}", b));
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
        print_str(location.file());
        print_str(":");
        print_integer(location.line());
        print_str(":");
        print_integer(location.column());
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

    /// Print debug information with a custom label
    fn deko_debug_with_label(&self, label: &str) {
        print_str(label);
        print_str(": ");
        self.deko_debug();
        print_char('\n');
    }
}

// Implement DekoDebug for basic types
impl DekoDebug for u8 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for u16 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for u32 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for u64 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for usize {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for i8 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for i16 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for i32 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for i64 {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for isize {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_integer(*self);
    }
}

impl DekoDebug for bool {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_bool(*self);
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
        print_char('"');
        print_str(self);
        print_char('"');
    }
}

impl<T> DekoDebug for *const T {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_address(*self);
    }
}

impl<T> DekoDebug for *mut T {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_address(*self as *const T);
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

// DekoDebug implementations for IgvmParamBlock types from deko-std
#[cfg(feature = "logging")]
impl DekoDebug for deko_std::boot::IgvmParamBlock {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("IgvmParamBlock {\n");

        print_str("  param_area_size: ");
        print_integer(self.param_area_size);
        print_str(",\n");

        print_str("  debug_serial_port: 0x");
        print_integer_hex(self.debug_serial_port);
        print_str(",\n");

        print_str("  use_alternate_injection: ");
        print_bool(self.use_alternate_injection != 0);
        print_str(",\n");

        print_str("  vtom: 0x");
        print_integer_hex(self.vtom);
        print_str(",\n");

        print_str("  kernel_base: 0x");
        print_integer_hex(self.kernel_base);
        print_str(",\n");

        print_str("  kernel_min_size: ");
        print_integer(self.kernel_min_size);
        print_str(",\n");

        print_str("  kernel_max_size: ");
        print_integer(self.kernel_max_size);
        print_str(",\n");

        print_str("  stage1_size: ");
        print_integer(self.stage1_size);
        print_str(",\n");

        print_str("  stage1_base: 0x");
        print_integer_hex(self.stage1_base);
        print_str(",\n");

        print_str("  firmware: ");
        self.firmware.deko_debug();
        print_str(",\n");

        print_char('}');
    }
}

#[cfg(feature = "logging")]
impl DekoDebug for deko_std::boot::IgvmParamBlockFwInfo {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("IgvmParamBlockFwInfo {\n");

        print_str("    start: 0x");
        print_integer_hex(self.start);
        print_str(",\n");

        print_str("    size: ");
        print_integer(self.size);
        print_str(",\n");

        print_str("    in_low_memory: ");
        print_bool(self.in_low_memory != 0);
        print_str(",\n");

        print_str("    secrets_page: 0x");
        print_integer_hex(self.secrets_page);
        print_str(",\n");

        print_str("    cpuid_page: 0x");
        print_integer_hex(self.cpuid_page);
        print_str(",\n");

        print_str("    prevalidated_count: ");
        print_integer(self.prevalidated_count);
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

#[cfg(feature = "logging")]
impl DekoDebug for deko_std::boot::IgvmParamBlockFwMem {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("{ base: 0x");
        print_integer_hex(self.base);
        print_str(", size: ");
        print_integer(self.size);
        print_str(" }");
    }
}

// DekoDebug implementations for DekoCtx and related types
#[cfg(feature = "logging")]
impl DekoDebug for crate::cpu::ctx::DekoCtx {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("DekoCtx {\n");

        print_str("  stage2_launch_info: ");
        print_address(self.stage2_launch_info.addr() as *const ());
        print_str(",\n");

        print_str("  pgtable: ");
        print_address(self.pgtable.addr() as *const ());
        print_str(",\n");

        print_str("  gdt: ");
        print_address(self.gdt.addr() as *const ());
        print_str(",\n");

        print_str("  mapping_space: ");
        self.mapping_space.deko_debug();
        print_str(",\n");

        print_char('}');
    }
}

// DekoDebug implementation for MappingSpace from deko-std
#[cfg(feature = "logging")]
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
#[cfg(feature = "logging")]
impl DekoDebug for deko_std::address::FixedAddressMappingRange {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("FixedAddressMappingRange {\n");

        print_str("      virt_start: 0x");
        print_integer_hex(self.virt_start.0);
        print_str(",\n");

        print_str("      virt_end: 0x");
        print_integer_hex(self.virt_end.0);
        print_str(",\n");

        print_str("      phys_start: 0x");
        print_integer_hex(self.phys_start.0);
        print_str(",\n");

        print_str("    }");
    }
}

// DekoDebug implementation for DekoCpuCore from deko-std
#[cfg(feature = "logging")]
impl DekoDebug for deko_std::cpu::DekoCpuCore {
    #[verifier::external_body]
    fn deko_debug(&self) {
        print_str("DekoCpuCore {\n");

        print_str("    heap_mapping: ");
        self.valid_heap_mapping_range().deko_debug();
        print_str(",\n");

        print_str("    kernel_mapping: ");
        self.valid_kernel_mapping_range().deko_debug();
        print_str(",\n");

        print_str("  }");
    }
}

} // verus!

// Ergonomic macros for debugging with DekoDebug trait

/// Debug print macro using DekoDebug trait
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! deko_dbg {
    () => {
        $crate::logging::print_str_ln("");
    };
    ($val:expr $(,)?) => {
        {
            $crate::logging::print_str("[DBG] ");
            $crate::logging::print_str(stringify!($val));
            $crate::logging::print_str(" = ");
            $val.deko_debug();
            $crate::logging::print_char('\n');
        }
    };
    ($($val:expr),+ $(,)?) => {
        {
            $crate::logging::print_str("[DBG] ");
            $(
                $crate::logging::print_str(stringify!($val));
                $crate::logging::print_str(" = ");
                $val.deko_debug();
                $crate::logging::print_str(", ");
            )+
            $crate::logging::print_char('\n');
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! deko_dbg {
    ($($arg:tt)*) => {};
}

/// Print with DekoDebug and custom label
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! deko_print {
    ($label:expr, $val:expr) => {
        $val.deko_debug_with_label($label)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! deko_print {
    ($label:expr, $val:expr) => {};
}

/// Simple string print macro (no formatting support due to Verus restrictions)
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_str {
    ($s:expr) => {
        $crate::logging::print_str($s)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_str {
    ($s:expr) => {};
}

/// Print string with newline
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_str_ln {
    ($s:expr) => {
        $crate::logging::print_str_ln($s)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_str_ln {
    ($s:expr) => {};
}

/// Integer printing macros
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_int {
    ($val:expr) => {
        $crate::logging::print_integer($val)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_int {
    ($val:expr) => {};
}

/// Hexadecimal printing macros
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_hex {
    ($val:expr) => {
        $crate::logging::print_integer_hex($val)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_hex {
    ($val:expr) => {};
}

/// Hexadecimal with prefix printing macros
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_hex_prefixed {
    ($val:expr) => {
        $crate::logging::print_integer_hex_prefixed($val)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_hex_prefixed {
    ($val:expr) => {};
}

/// Binary printing macro
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_bin {
    ($val:expr) => {
        $crate::logging::print_integer_binary($val)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_bin {
    ($val:expr) => {};
}

/// Float printing macros
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_float {
    ($val:expr) => {
        $crate::logging::print_float_decimal($val)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_float {
    ($val:expr) => {};
}

/// Memory dump macro
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_hex_dump {
    ($data:expr) => {
        $crate::logging::print_hex_dump($data, 16)
    };
    ($data:expr, $bytes_per_line:expr) => {
        $crate::logging::print_hex_dump($data, $bytes_per_line)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_hex_dump {
    ($data:expr $(, $bytes_per_line:expr)?) => {};
}

/// Address printing macro
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_addr {
    ($ptr:expr) => {
        $crate::logging::print_address($ptr)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_addr {
    ($ptr:expr) => {};
}

/// Conditional string printing
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_if {
    ($cond:expr, $s:expr) => {
        if $cond {
            $crate::logging::print_str_ln($s);
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_if {
    ($cond:expr, $s:expr) => {};
}

/// Error logging - supports multiple string arguments
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_error {
    ($($s:expr),+ $(,)?) => {
        {
            $crate::logging::print_str($crate::logging::ERROR_COLOR);
            $crate::logging::print_str("[ERROR] ");
            $(
                $crate::logging::print_str($s);
            )+
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_char('\n');
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_error {
    ($($s:expr),+ $(,)?) => {};
}

/// Warning logging - supports multiple string arguments  
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_warn {
    ($($s:expr),+ $(,)?) => {
        {
            $crate::logging::print_str($crate::logging::WARN_COLOR);
            $crate::logging::print_str("[WARN] ");
            $(
                $crate::logging::print_str($s);
            )+
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_char('\n');
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_warn {
    ($($s:expr),+ $(,)?) => {};
}

/// Info logging - supports multiple string arguments
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_info {
    ($($s:expr),+ $(,)?) => {
        {
            $crate::logging::print_str($crate::logging::INFO_COLOR);
            $crate::logging::print_str("[INFO] ");
            $(
                $crate::logging::print_str($s);
            )+
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_char('\n');
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_info {
    ($($s:expr),+ $(,)?) => {};
}

/// Debug logging - supports multiple string arguments
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_debug {
    ($($s:expr),+ $(,)?) => {
        {
            $crate::logging::print_str($crate::logging::DEBUG_COLOR);
            $crate::logging::print_str("[DEBUG] ");
            $(
                $crate::logging::print_str($s);
            )+
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_char('\n');
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_debug {
    ($($s:expr),+ $(,)?) => {};
}

/// Trace logging - supports multiple string arguments
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_trace {
    ($($s:expr),+ $(,)?) => {
        {
            $crate::logging::print_str($crate::logging::TRACE_COLOR);
            $crate::logging::print_str("[TRACE] ");
            $(
                $crate::logging::print_str($s);
            )+
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::logging::print_char('\n');
        }
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_trace {
    ($($s:expr),+ $(,)?) => {};
}

/// Helper macro for inline hex formatting using lexical
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! hex {
    ($val:expr) => {{
        // Create a temporary buffer (18 bytes: "0x" + 16 hex digits)
        $crate::logging::__hex($val, &mut buffer)
    }};
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! hex {
    ($val:expr) => {
        ""
    };
}

/// Print hex value with 0x prefix inline
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! hex_pfx {
    ($val:expr) => {{
        // This is a bit ugly, but we need to concatenate "0x" with the hex value
        // For now, users need to manually include "0x" in their log calls
        $crate::hex!($val)
    }};
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! hex_pfx {
    ($val:expr) => {
        ""
    };
}

/// Print decimal value inline
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! dec {
    ($val:expr) => {{
        let mut buffer = itoa::Buffer::new();
        buffer.format($val)
    }};
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! dec {
    ($val:expr) => {
        ""
    };
}

/// Print the kernel banner with build information
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_banner {
    () => {
        $crate::logging::print_banner()
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_banner {
    () => {};
}

/// Print panic information with build context
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! log_panic {
    ($info:expr) => {
        $crate::logging::print_panic_info($info)
    };
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! log_panic {
    ($info:expr) => {};
}

#[cfg(not(feature = "logging"))]
verus! {

#[verifier::external_body]
#[inline]
pub fn print_str(out: &str) {
}

} // verus!
