use deko_macros::DekoDebug;
use vstd::prelude::*;

verus! {

#[derive(DekoDebug)]
pub struct DekoLabelId {
    pub id: u32,
}

/// The lattice label in the information flow control logic with a label id
/// attached to identify different isolation domains.
#[derive(DekoDebug)]
pub enum DekoLabel {
    Low(DekoLabelId),
    High(DekoLabelId),
}

} // verus!
