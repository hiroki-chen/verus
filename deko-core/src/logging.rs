//! Debug logging feature for the monitor; enable only for debugging purposes only. You should disable this for safety reasons.
//!
//! This crate currently DOES NOT use the `vstd` crate to verify its implementation as it is designed solely for debugging.
//!
//! TODO: Overhaul this module to fit both snp and tdx.
use core::fmt::Write;

use deko_std::prelude::*;
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

const RESET_COLOR: &'static str = "\x1B[0m";

const ERROR_COLOR: &'static str = "\x1B[31m";

// Red
const WARN_COLOR: &'static str = "\x1B[33m";

// Yellow
const INFO_COLOR: &'static str = "\x1B[32m";

// Green
const DEBUG_COLOR: &'static str = "\x1B[34m";

// Blue
const TRACE_COLOR: &'static str = "\x1B[36m";

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
fn __print(arg: core::fmt::Arguments) {
    let (mut console, write_handle) = CONSOLE.acquire_write();
    console.write_fmt(arg).unwrap();
    write_handle.release_write(console);
}

} // verus!
#[cfg(feature = "logging")]
verus! {

#[verifier::external_body]
#[inline]
pub fn print_str(out: &str) {
    __print(format_args!("{}", out));
}

} // verus!
#[cfg(not(feature = "logging"))]
verus! {

#[verifier::external_body]
#[inline]
pub fn print_str(out: &str) {
}

} // verus!
