use deko_std::address::VirtAddr;
use deko_std::wf::WellFormed;
use vstd::map::Map;
use vstd::prelude::*;

use crate::snp::RmpFlags;

verus! {

/// A tracked struct for tracking all RMP table entries and their flags.
///
/// TODO: Insert this struct into `DekoCpuCtxPermission`.
pub tracked struct DekoRmpTablePermission {
    /// A map from virtual addresses to RMP flags.
    pub table: Map<VirtAddr, RmpFlags>,
}

impl DekoRmpTablePermission {
    pub open spec fn translates_all_valid_addresses(self) -> bool {
        true
    }
}

impl WellFormed for DekoRmpTablePermission {
    open spec fn wf(&self) -> bool {
        &&& forall|addr: VirtAddr|
            #![trigger self.table[addr]]
            self.table.contains_key(addr) ==> self.table[addr].wf()
    }
}

} // verus!
