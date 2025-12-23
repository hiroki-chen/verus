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

// Log level information - populated by build.rs
pub const LOG_LEVEL: &'static str = env!("DEKO_LOG_LEVEL");

pub exec const LOG_LEVEL_NUM: usize = {
    let level_str = env!("DEKO_LOG_LEVEL_NUM");
    match level_str {
        "1" => 1,
        "2" => 2,
        "3" => 3,
        "4" => 4,
        "5" => 5,
        _ => 3,  // Default to INFO
    }
};

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

pub const CONSOLE: Console = Console;

// Now we need a lock to protect concurrent access to the console.
pub exec static CONSOLE_LOCK: DekoSimpleRwLock<()>
    ensures
        CONSOLE_LOCK.wf(),
{
    let r = DekoSimpleRwLock::new(DekoAtomicData::new(()), (), Ghost(TrivialPredicate::new()));

    proof {
        use_type_invariant(&r);
    }

    r
}

impl WellFormed for Console {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl Console {
    fn write_bytes(&self, buffer: &[u8]) {
        let ghcb_port = match GHCB_IO_PORT.get() {
            Some(p) => p,
            None => return ,
        };

        for b in 0..buffer.len()
            invariant
                ghcb_port.wf(),
        {
            // Better not to call `.get()` inside
            // the loop as this will create race
            // condition so that we cannot print
            // anything from the port.
            ghcb_port.outb(buffer[b]);
        }
    }
}

#[verifier::external_body]
pub fn print_str(s: &str)
    opens_invariants none
    no_unwind
{
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

    print_str("\n");
    print_str(ERROR_COLOR);
    print_str("=== SYSTEM HALTED ===\n");
    print_str(RESET_COLOR);
}

} // verus!
#[macro_export]
macro_rules! print_with_format {
    ($expr:expr => hex) => {{
        use deko_std::prelude::DekoDebug;
        $expr.deko_debug_hex(&$crate::logging::CONSOLE);
    }};
    ($expr:expr => oct) => {{
        use deko_std::prelude::DekoDebug;
        $expr.deko_debug_oct(&$crate::logging::CONSOLE);
    }};
    ($expr:expr => dec) => {{
        use deko_std::prelude::DekoDebug;
        $expr.deko_debug(&$crate::logging::CONSOLE);
    }};

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
    ($expr:expr) => {{
        use deko_std::prelude::DekoDebug;
        $expr.deko_debug(&$crate::logging::CONSOLE);
    }};
}

// Internal macro for variadic argument processing
#[macro_export]
macro_rules! print_args_internal {
    // Base case - no arguments
    () => {};

    // Single argument with format specifier
    ($arg:expr => $fmt:ident) => {
        $crate::print_with_format!($arg => $fmt);
    };
    ($arg:expr => $fmt:ident($param:literal)) => {
        $crate::print_with_format!($arg => $fmt($param));
    };

    // Single argument without format specifier
    ($arg:expr) => {
        $crate::print_with_format!($arg);
    };

    // Multiple arguments - first with format specifier
    ($head:expr => $fmt:ident, $($tail:tt)*) => {
        $crate::print_with_format!($head => $fmt);
        $crate::logging::print_str(" ");
        $crate::print_args_internal!($($tail)*);
    };
    ($head:expr => $fmt:ident($param:literal), $($tail:tt)*) => {
        $crate::print_with_format!($head => $fmt($param));
        $crate::logging::print_str(" ");
        $crate::print_args_internal!($($tail)*);
    };

    // Multiple arguments - first without format specifier
    ($head:expr, $($tail:tt)*) => {
        $crate::print_with_format!($head);
        $crate::logging::print_str(" ");
        $crate::print_args_internal!($($tail)*);
    };
}

// Should be defined outside verus! block to allow macro export
// otherwise the macro hygiene will complain about $crate usage.
#[macro_export]
macro_rules! kinfo {
    ($($args:tt)*) => {
        #[cfg(all(feature = "logging", log_level_info))]
        {
            let _guard = $crate::logging::CONSOLE_LOCK.acquire_write();

            $crate::logging::print_str($crate::logging::INFO_COLOR);
            $crate::logging::print_str("[INFO] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");

            _guard.release_write_no_val();
        }
    };
}

#[macro_export]
macro_rules! kwarn {
    ($($args:tt)*) => {
        #[cfg(all(feature = "logging", log_level_warn))]
        {
            let _guard = $crate::logging::CONSOLE_LOCK.acquire_write();

            $crate::logging::print_str($crate::logging::WARN_COLOR);
            $crate::logging::print_str("[WARN] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");

            _guard.release_write_no_val();
        }
    };
}

#[macro_export]
macro_rules! kerror {
    ($($args:tt)*) => {
        #[cfg(all(feature = "logging", log_level_error))]
        {
            let _guard = $crate::logging::CONSOLE_LOCK.acquire_write();

            $crate::logging::print_str($crate::logging::ERROR_COLOR);
            $crate::logging::print_str("[ERROR] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");

            _guard.release_write_no_val();
        }
    };
}

#[macro_export]
macro_rules! kdebug {
    ($($args:tt)*) => {
        #[cfg(all(feature = "logging", log_level_debug))]
        {
            let _guard = $crate::logging::CONSOLE_LOCK.acquire_write();

            $crate::logging::print_str($crate::logging::DEBUG_COLOR);
            $crate::logging::print_str("[DEBUG] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");

            _guard.release_write_no_val();
        }
    };
}

#[macro_export]
macro_rules! ktrace {
    ($($args:tt)*) => {
        #[cfg(all(feature = "logging", log_level_trace))]
        {
            let _guard = $crate::logging::CONSOLE_LOCK.acquire_write();

            $crate::logging::print_str($crate::logging::TRACE_COLOR);
            $crate::logging::print_str("[TRACE] ");
            $crate::logging::print_str($crate::logging::RESET_COLOR);
            $crate::print_args_internal!($($args)*);
            $crate::logging::print_str("\n");

            _guard.release_write_no_val();
        }
    };
}
