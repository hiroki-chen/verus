#![no_std]

use spin::Mutex;
use uart_16550::SerialPort;
use x86_64::instructions::interrupts::without_interrupts;
use x86_64::instructions::port::Port;

pub const COM0_ADDR: u16 = 0x3f8;
pub const COM1_ADDR: u16 = 0x2f8;
pub const SERIAL_COM_0_UUID: &str = "097e522c-6380-417d-9077-5b76565ba5be";
pub const SERIAL_COM_1_UUID: &str = "a7e92bf8-5991-45cf-b38a-7b3c8255cb14";

/// COM (communication port)[1][2] is the original, yet still common, name of the serial port interface on PC-compatible
/// computers. It can refer not only to physical ports, but also to emulated ports, such as ports created by Bluetooth or
/// USB adapters.
pub struct ComPort {
    serial_port: Mutex<SerialPort>,
    /// Base address: 0x*f8.
    addr: u16,
    /// UUID.
    uuid: &'static str,
}

impl ComPort {
    pub fn new(addr: u16, uuid: &'static str) -> Self {
        let serial_port = Mutex::new(unsafe { SerialPort::new(addr) });
        serial_port.lock().init();
        Self { serial_port, addr, uuid }
    }

    pub fn get_addr(&self) -> u16 { self.addr }

    /// Should not use keyboard interrupts.
    pub fn read(&self) -> u8 { 0 }

    pub fn write(&self, bytes: &[u8]) {
        // We should disable interrupts here.
        without_interrupts(|| {
            for byte in bytes.iter() {
                self.serial_port.lock().send(*byte);
            }
        });
    }

    pub fn enable_irq(&self) {
        let addr = self.addr;
        // Interrupt enable register.
        let mut ier = Port::<u8>::new(addr + 0x1);
        unsafe {
            ier.write(0x07);
        }
    }
}

pub fn init_serial_ports() {
    let com0 = ComPort::new(COM0_ADDR, SERIAL_COM_0_UUID);
    let com1 = ComPort::new(COM1_ADDR, SERIAL_COM_1_UUID);

    // Enable IRQs.
    com0.enable_irq();
    com1.enable_irq();
}
