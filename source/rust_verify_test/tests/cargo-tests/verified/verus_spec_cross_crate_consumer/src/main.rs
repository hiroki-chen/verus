use vstd::prelude::*;
use verus_spec_cross_crate_lib::*;

fn main() {
    // Test calling cross-crate function with verus_spec(with ...)
    // This should trigger the _VERUS_VERIFIED function lookup
    let result = #[verus_spec(with Tracked(2))] get_data(42);
    
    // Test calling another cross-crate function
    let processed = #[verus_spec(with Ghost(2))]  process_data(100);
}
