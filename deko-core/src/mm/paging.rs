use deko_std::prelude::*;
use vstd::prelude::*;

deko_bitflags! {
    pub struct Pte: u64 {
        const PRESENT       = 0;
        const WRITABLE      = 1;
        const USER          = 2;
        // const PWT           = 3;
        // const PCD           = 4;
        const ACCESSED      = 5;
        const DIRTY         = 6;
        const HUGE          = 7;
        const GLOBAL        = 8;
        const NX            = 63;
    }
}
