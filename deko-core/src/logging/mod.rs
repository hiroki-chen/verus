//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
#[cfg(feature = "logging")]
pub mod imp {
    use core::fmt;

    use vstd::prelude::*;

    verus! {

#[verifier::external]
pub fn init_logger() {
    deko_logging::init();
}

#[verifier::external]
pub fn log(level: log::Level, args: fmt::Arguments) {
    deko_logging::log(level, args);
}

#[macro_export]
        macro_rules! info {
            ($($arg:tt)*) => {
                log(log::Level::Info, format_args!($($arg)*));
            }
        }

#[macro_export]
        macro_rules! warn {
            ($($arg:tt)*) => {
                log(log::Level::Warn, format_args!($($arg)*));
            }

        }

#[macro_export]
        macro_rules! error {
            ($($arg:tt)*) => {
                log(log::Level::Error, format_args!($($arg)*));
            }
        }

} // verus!
}

#[cfg(not(feature = "logging"))]
pub mod imp {
    use vstd::prelude::*;

    verus! {

#[verifier::external]
pub fn init_logger() {
    // No-op if logging is disabled.
}

#[verifier::external]
pub fn log(_level: log::Level, _args: fmt::Arguments) {
    // No-op if logging is disabled.
}

#[macro_export]
        macro_rules! info {
            ($($arg:tt)*) => {};
        }

#[macro_export]
        macro_rules! warn {
            ($($arg:tt)*) => {};
        }

#[macro_export]
        macro_rules! error {
            ($($arg:tt)*) => {};
        }

} // verus!
}

#[allow(unused_imports)]
pub use imp::*;
