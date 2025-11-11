//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
//!
//! TODO: Overhaul this module to fit both snp and tdx.
use core::fmt::Write;

use deko_std::prelude::*;
#[cfg(feature = "logging")]
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
pub const DEKO_BANNER: &'static str =
    r#"

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

pub(crate) const CONSOLE: Console = Console;

impl WellFormed for Console {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl Console {
    #[verifier::external_body]
    fn write_bytes(&self, buffer: &[u8]) {
        let ghcb_port = match GHCB_IO_PORT.get() {
            Some(p) => p,
            None => return ,
        };

        for b in buffer.iter() {
            // Better not to call `.get()` inside
            // the loop as this will create race
            // condition so that we cannot print
            // anything from the port.
            ghcb_port.outb(*b);
        }
    }
}

#[verifier::external_body]
pub(crate) fn print_str(s: &str) {
    CONSOLE.write_bytes(s.as_bytes());
}

impl deko_std::fmt::DekoWriter for Console {
    #[verifier::external_body]
    fn write_str(&self, s: &str) {
        self.write_bytes(s.as_bytes());
    }

    #[verifier::external_body]
    fn write_char(&self, c: char) {
        let mut buffer = [0u8;4];
        let s: &mut str = c.encode_utf8(&mut buffer);
        self.write_str(s);
    }

    #[verifier::external_body]
    fn write_bytes(&self, bytes: &[u8]) {
        self.write_bytes(bytes);
    }
}

} // verus!
#[cfg(feature = "logging")]
verus! {

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
        location.file().deko_debug(&CONSOLE);
        print_str(":");
        location.line().deko_debug(&CONSOLE);
        print_str(":");
        location.column().deko_debug(&CONSOLE);
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

// impl DekoDebug for deko_std::address::VirtAddr {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("VirtAddr(");
//         self.0.deko_debug_hex();
//         print_char(')');
//     }
//     #[verifier::external_body]
//     fn deko_debug_hex(&self) {
//         self.deko_debug();
//     }
// }
// impl DekoDebug for deko_std::address::PhysAddr {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("PhysAddr(");
//         self.0.deko_debug_hex();
//         print_char(')');
//     }
//     #[verifier::external_body]
//     fn deko_debug_hex(&self) {
//         self.deko_debug();
//     }
// }
// impl DekoDebug for deko_std::boot::IgvmParamBlock {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("IgvmParamBlock {\n");
//         print_str("  param_area_size: ");
//         debug_packed_field!(self, param_area_size, deko_debug);
//         print_str(",\n");
//         print_str("  debug_serial_port: ");
//         debug_packed_field!(self, debug_serial_port, deko_debug_hex);
//         print_str(",\n");
//         print_str("  use_alternate_injection: ");
//         let use_alternate_injection = self.use_alternate_injection;
//         (use_alternate_injection != 0).deko_debug();
//         print_str(",\n");
//         print_str("  vtom: ");
//         debug_packed_field!(self, vtom, deko_debug_hex);
//         print_str(",\n");
//         print_str("  kernel_base: ");
//         debug_packed_field!(self, kernel_base, deko_debug_hex);
//         print_str(",\n");
//         print_str("  kernel_min_size: ");
//         debug_packed_field!(self, kernel_min_size, deko_debug);
//         print_str(",\n");
//         print_str("  kernel_max_size: ");
//         debug_packed_field!(self, kernel_max_size, deko_debug);
//         print_str(",\n");
//         print_str("  stage1_size: ");
//         debug_packed_field!(self, stage1_size, deko_debug);
//         print_str(",\n");
//         print_str("  stage1_base: ");
//         debug_packed_field!(self, stage1_base, deko_debug_hex);
//         print_str(",\n");
//         print_str("  firmware: ");
//         debug_packed_field!(self, firmware, deko_debug);
//         print_str(",\n");
//         print_char('}');
//     }
// }
// impl DekoDebug for deko_std::boot::IgvmParamBlockFwInfo {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("IgvmParamBlockFwInfo {\n");
//         print_str("    start: ");
//         debug_packed_field!(self, start, deko_debug_hex);
//         print_str(",\n");
//         print_str("    size: ");
//         debug_packed_field!(self, size, deko_debug);
//         print_str(",\n");
//         print_str("    in_low_memory: ");
//         (self.in_low_memory != 0).deko_debug();
//         print_str(",\n");
//         print_str("    secrets_page: ");
//         debug_packed_field!(self, secrets_page, deko_debug_hex);
//         print_str(",\n");
//         print_str("    cpuid_page: ");
//         debug_packed_field!(self, cpuid_page, deko_debug_hex);
//         print_str(",\n");
//         print_str("    prevalidated_count: ");
//         debug_packed_field!(self, prevalidated_count, deko_debug);
//         print_str(",\n");
//         print_str("    prevalidated: [");
//         for i in 0..8 {
//             if i < self.prevalidated_count {
//                 if i > 0 {
//                     print_str(", ");
//                 }
//                 // Access array element safely
//                 self.prevalidated.0[i as usize].deko_debug();
//             }
//         }
//         print_str("]\n");
//         print_str("  }");
//     }
// }
// impl DekoDebug for deko_std::boot::IgvmParamBlockFwMem {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("{ base: ");
//         debug_packed_field!(self, base, deko_debug_hex);
//         print_str(", size: ");
//         debug_packed_field!(self, size, deko_debug);
//         print_str(" }");
//     }
// }
// // DekoDebug implementations for DekoCtx and related types
// impl DekoDebug for crate::cpu::ctx::DekoCtx {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("DekoCtx {\n");
//         print_str("  stage2_launch_info: ");
//         (self.stage2_launch_info.addr() as usize).deko_debug_hex();
//         print_str(",\n");
//         print_str("  pgtable: ");
//         (self.pgtable.addr() as usize).deko_debug_hex();
//         print_str(",\n");
//         print_str("  gdt: ");
//         (self.gdt.addr() as usize).deko_debug_hex();
//         print_str(",\n");
//         print_str("  mapping_space: ");
//         self.mapping_space.deko_debug();
//         print_str(",\n");
//         print_char('}');
//     }
// }
// // DekoDebug implementation for MappingSpace from deko-std
// impl DekoDebug for deko_std::address::MappingSpace {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("MappingSpace {\n");
//         print_str("    kernel: ");
//         self.kernel.deko_debug();
//         print_str(",\n");
//         print_str("    physmap: ");
//         self.physmap.deko_debug();
//         print_str(",\n");
//         print_str("  }");
//     }
// }
// // DekoDebug implementation for FixedAddressMappingRange from deko-std
// impl DekoDebug for deko_std::address::FixedAddressMappingRange {
//     #[verifier::external_body]
//     fn deko_debug(&self) {
//         print_str("FixedAddressMappingRange {\n");
//         print_str("      virt_start: ");
//         self.virt_start.0.deko_debug_hex();
//         print_str(",\n");
//         print_str("      virt_end: ");
//         self.virt_end.0.deko_debug_hex();
//         print_str(",\n");
//         print_str("      phys_start: ");
//         self.phys_start.0.deko_debug_hex();
//         print_str(",\n");
//         print_str("    }");
//     }
// }
macro_rules! print_with_format {
    ($expr:expr => hex) => {
        {
            use deko_std::prelude::DekoDebug;
            $expr.deko_debug_hex(& $crate::logging::CONSOLE);
        }
    };
    ($expr:expr => oct) => {
        {
            use deko_std::prelude::DekoDebug;
            $expr.deko_debug_oct(& $crate::logging::CONSOLE);
        }
    };
    ($expr:expr => dec) => {
        {
            use deko_std::prelude::DekoDebug;
            $expr.deko_debug(& $crate::logging::CONSOLE);
        }
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
            use deko_std::prelude::DekoDebug;
            $expr.deko_debug(& $crate::logging::CONSOLE);
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

pub(crate) use {print_args_internal, print_with_format};
