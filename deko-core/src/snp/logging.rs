//! This debugging tool implements logging functionality for SNP guests.
//!
//! Since SNP does not allow direct print to console,
//! we will need to leverage the GHCB protocol for this purpose.
//!
//! Also notice that SNP has very poor support for debugging using gdb so it'd better
//! to use logging. Also notice that logging is extremely dangerous as this could
//! interfere with information flow control. So it should only be enabled on debug.
use deko_std::prelude::*;
#[cfg(feature = "logging")]
use deko_std::snp::ghcb::*;
use vstd::prelude::*;

use crate::snp::ghcb::current_ghcb;
#[cfg(feature = "logging")]
use crate::snp::ghcb::*;
use crate::snp::Snp;

#[cfg(feature = "logging")]
verus! {

pub const LOGGING_BANNER: &'static str = 
r#"
██████╗ ███████╗██╗  ██╗ ██████╗ 
██╔══██╗██╔════╝██║ ██╔╝██╔═══██╗
██║  ██║█████╗  █████╔╝ ██║   ██║
██║  ██║██╔══╝  ██╔═██╗ ██║   ██║
██████╔╝███████╗██║  ██╗╚██████╔╝
╚═════╝ ╚══════╝╚═╝  ╚═╝ ╚═════╝ 
"#;

pub const SERIAL_PORT: u16 = 0x3f8;

const BAUD: u32 = 9600;

const DLAB: u8 = 0x80;

pub const TXR: u16 = 0;

// Transmit register
pub const _RXR: u16 = 0;

// Receive register
pub const IER: u16 = 1;

// Interrupt enable
pub const _IIR: u16 = 2;

// Interrupt ID
pub const FCR: u16 = 2;

// FIFO Control
pub const LCR: u16 = 3;

// Line Control
pub const MCR: u16 = 4;

// Modem Control
pub const LSR: u16 = 5;

// Line Status
pub const _MSR: u16 = 6;

// Modem Status
pub const DLL: u16 = 0;

// Divisor Latch Low
pub const DLH: u16 = 1;

// Divisor Latch High
pub const RCVRDY: u8 = 0x01;

pub const XMTRDY: u8 = 0x20;

pub struct GHCBIoPortPred;

impl Predicate<GHCBIoPort> for GHCBIoPortPred {
    #[verifier::inline]
    open spec fn inv(self, ghcb_io_port: GHCBIoPort) -> bool {
        ghcb_io_port.wf()
    }
}

pub exec static GHCB_IO_PORT: OnceCell<GHCBIoPort, GHCBIoPortPred>
    ensures
        GHCB_IO_PORT.wf(),
{
    OnceCell::new(Ghost(GHCBIoPortPred {  }))
}

/// A struct to represent the GHCB I/O port.
///
/// # Note
///
/// This struct does not lock the I/O port and it is not intended
/// to be use directly. We must wrap it through a struct, e.g.,
/// `Terminal` or `Console` that finally re-routes all the request
/// to this struct.
///
/// Furthermore, since Verus does not yet support trait objects,
/// we can only use the concrete types directly via a dispatcher.
#[derive(Clone, Copy)]
pub struct GHCBIoPort(u16);

impl WellFormed for GHCBIoPort {
    closed spec fn wf(&self) -> bool {
        // Maximum offset is 7
        self.0 + 8 <= u16::MAX
    }
}

impl GHCBIoPort {
    pub closed spec fn valid_port(&self, port: u16) -> bool {
        self.0 + port as u16 <= u16::MAX
    }

    pub fn new(port: u16) -> (r: Self)
        requires
            port + 8 <= u16::MAX,
        ensures
            r.wf(),
    {
        GHCBIoPort(port)
    }

    pub fn init(&self)
        requires
            self.wf(),
    {
        let divisor: u32 = 115200 / BAUD;

        self.outb_port(LCR, 0x3);  // 8n1
        self.outb_port(IER, 0x0);  // No Interrupt
        self.outb_port(FCR, 0x0);  // No FIFO
        self.outb_port(MCR, 0x3);  // DTR + RTS

        // ghcb might still be problematic.
        self.outb_port(LCR, 0x03 | DLAB);
        self.outb_port(DLL, (divisor & 0xff) as u8);
        self.outb_port(DLH, ((divisor >> 8) & 0xff) as u8);
        self.outb_port(LCR, 0x03 & !DLAB);
    }

    fn outb_port(&self, port: u16, value: u8)
        requires
            self.wf(),
            self.valid_port(port),
    {
        let (current_ghcb, Tracked(current_ghcb_perm)) = current_ghcb();

        GuestHostCommucationBlock::ioout(
            current_ghcb,
            Tracked(current_ghcb_perm),
            self.0 + port,
            value as u64,
            core::mem::size_of::<u8>() as u8,
        );
    }

    fn inb_port(&self, port: u16) -> (r: u8)
        requires
            self.wf(),
            self.valid_port(port),
    {
        let (current_ghcb, Tracked(current_ghcb_perm)) = current_ghcb();

        GuestHostCommucationBlock::ioin(
            current_ghcb,
            Tracked(current_ghcb_perm),
            self.0 + port,
            1,
        ) as u8
    }

    #[inline(always)]
    pub fn outb(&self, value: u8)
        requires
            self.wf(),
    {
        self.outb_port(0, value);
    }

    pub fn inb(&self) {
        vstd::vpanic!("Not implemented");
    }
}

impl Snp {
    /// Initialize the GHCB logging mechanism.
    pub(crate) fn init_ghcb_logging(serial_port: u16)
        requires
            serial_port + 8 <= u16::MAX,
    {
        let v = GHCBIoPort::new(0x3f8);
        v.init();

        GHCB_IO_PORT.init(v);
    }
}

} // verus!
#[cfg(not(feature = "logging"))]
verus! {


} // verus!
