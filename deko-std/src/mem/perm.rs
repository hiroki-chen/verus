use vstd::prelude::*;

verus! {

/// A tracked enum for tracking the read/write permission on a given piece of memory.
///
/// TODO: Design privilege.
pub enum PermissionDekoMem {
    Foo,
}

impl PermissionDekoMem {
    /// Check if the permission is well-formed.
    pub open spec fn wf(&self) -> bool {
        true
        // TODO: Implement me!

    }
}

} // verus!
