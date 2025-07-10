#![no_std]

// In some module, e.g., your main lib.rs or a new logger.rs

use core::fmt;
use core::fmt::Write;

use log::{Level, LevelFilter, Metadata, Record};
use spin::Mutex;
use uart_16550::SerialPort;

const RESET_COLOR: &str = "\x1B[0m";
const ERROR_COLOR: &str = "\x1B[31m"; // Red
const WARN_COLOR: &str = "\x1B[33m"; // Yellow
const INFO_COLOR: &str = "\x1B[32m"; // Green
const DEBUG_COLOR: &str = "\x1B[34m"; // Blue
const TRACE_COLOR: &str = "\x1B[36m"; // Cyan

pub struct Logger {
    // The serial port is wrapped in a Mutex for safe concurrent access.
    port: Mutex<SerialPort>,
}

// Implement the `Log` trait for our Logger. This is what the `log`
// crate will call.
impl log::Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        // We can enable logs based on their level here if we want.
        // For now, let's enable everything.
        true
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let mut port = self.port.lock();

            // 1. Write the color code.
            // The `write!` macro is perfect for this too.
            let _ = write!(
                port,
                "{}",
                match record.level() {
                    Level::Error => ERROR_COLOR,
                    Level::Warn => WARN_COLOR,
                    Level::Info => INFO_COLOR,
                    Level::Debug => DEBUG_COLOR,
                    Level::Trace => TRACE_COLOR,
                }
            );

            // 2. THIS IS THE CRITICAL FIX:
            //    Use the `write!` macro to stream the formatted arguments
            //    directly to the serial port.
            let _ = write!(port, "{}", *record.args());

            // 3. Write the reset code and a newline.
            let _ = writeln!(port, "{}", RESET_COLOR);
        }
    }

    fn flush(&self) {}
}

// Global static instance of our logger.
static LOGGER: Logger = Logger {
    // The COM1 port address is 0x3F8. This is a standard.
    // The `SerialPort::new` function is `const`, so we can use it in a static.
    port: Mutex::new(unsafe { SerialPort::new(0x3F8) }),
};

// Public function to initialize the logging system.
pub fn init() {
    // Before we set the logger, we must initialize the serial port hardware.
    LOGGER.port.lock().init();

    // Set our custom logger as the global logger.
    log::set_logger(&LOGGER).unwrap();

    // Set the maximum log level.
    log::set_max_level(LevelFilter::Trace); // Log everything.

    log::info!("[DEKO-Monitor] Logger initialized successfully!");
}

pub fn log(level: Level, args: fmt::Arguments) {
    // This is the correct, panic-free way to log from a function
    // that receives fmt::Arguments.

    // 1. Build a log Record manually.
    //    We explicitly give our `args` to the builder. The logger backend
    //    knows how to consume this directly without re-formatting it.
    let record = Record::builder()
        .args(args)
        .level(level)
        .target(module_path!()) // or some other useful target
        .build();

    // 2. Send the record directly to the initialized logger.
    log::logger().log(&record);
}
