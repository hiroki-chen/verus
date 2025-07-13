//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
use vstd::prelude::*;

#[cfg(feature = "logging")]
mod warning {
    #![deprecated = "
        Logging is an unverified feature and should not be enabled in production code.
        It is only used for debugging purposes.
    "]
}

verus! {

#[verifier::external_body]
#[cfg(feature = "logging")]
pub fn init_logger() {
    #[allow(unused_imports)]
    use self::warning;

    deko_logging::init();
}

#[verifier::external_body]
#[cfg(not(feature = "logging"))]
pub fn init_logger() {
    // No-op if logging is disabled.
}

#[verifier::external]
#[cfg(feature = "logging")]
pub fn log(level: log::Level, args: core::fmt::Arguments) {
    deko_logging::log(level, format_args!("[DEKO-Monitor] {}", args));
}

} // verus!
#[cfg(feature = "logging")]
#[macro_export]
macro_rules! info {
    ($($arg:tt)*) => {
        $crate::logging::log(log::Level::Info, format_args!($($arg)*));
    }
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! info {
    ($($arg:tt)*) => {
        let _ = format_args!($($arg)*);
    };
}

#[cfg(feature = "logging")]
#[macro_export]
macro_rules! warn {
    ($($arg:tt)*) => {
        log(log::Level::Warn, format_args!($($arg)*));
    }
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! warn {
    ($($arg:tt)*) => {
        let _ = format_args!($($arg)*);
    }
}

#[cfg(feature = "logging")]
#[macro_export]
macro_rules! error {
    ($($arg:tt)*) => {
        log(log::Level::Error, format_args!($($arg)*));
    }
}

#[cfg(not(feature = "logging"))]
#[macro_export]
macro_rules! error {
    ($($arg:tt)*) => {
        let _ = format_args!($($arg)*);
    }
}
