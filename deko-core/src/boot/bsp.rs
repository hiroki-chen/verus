use vstd::prelude::*;

use crate::cpu::types::CpuCoreIdPerm;

verus! {

/// The entry to the Application Processors for SMP systems.
#[no_mangle]
pub extern "C" fn ap_entry() {
}

/// The entry to the Boot Strap Processor for SMP systems.
#[no_mangle]
#[verifier(external_body)]
pub extern "C" fn bsp_entry(Tracked(ap_ids): Tracked<Map<int, CpuCoreIdPerm>>) {
}

} // verus!
