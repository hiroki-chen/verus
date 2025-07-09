use vstd::prelude::*;

use crate::ptr::DekoPtrDestRaw;

verus! {

pub tracked struct Header {
    header_raw: DekoPtrDestRaw,
}

} // verus!
