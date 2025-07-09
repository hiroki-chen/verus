#![no_std]

// In some module, e.g., your main lib.rs or a new logger.rs

use core::fmt;

use log::{Level, LevelFilter, Metadata, Record, SetLoggerError};
use spin::Mutex;
use uart_16550::SerialPort;

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

            match record.level() {
                Level::Error => port.send(b'E'),
                Level::Warn => port.send(b'W'),
                Level::Info => port.send(b'I'),
                Level::Debug => port.send(b'D'),
                Level::Trace => port.send(b'T'),
            }

            // Send a space after the log level.
            port.send(b' ');

            // Write each byte of the string to the serial port.
            for byte in record.args().as_str().unwrap().bytes() {
                // Write the byte to the serial port.
                port.send(byte);
            }
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
    loop {}

    // Set our custom logger as the global logger.
    log::set_logger(&LOGGER);

    // Set the maximum log level.
    log::set_max_level(LevelFilter::Trace); // Log everything.

    // Now we can use the log macros!
    log::info!("Logger initialized!");
}

pub fn log(level: Level, args: fmt::Arguments) {
    // This function can be used to log messages directly.
    // It will use the global logger we set up.
    log::log!(level, "{}", args);
}
