use vstd::prelude::*;

verus! {

pub const ALLOWED_SHARED_FILES: [&'static str; 3] = [
    "/lib/x86_64-linux-gnu/libc.so.6",
    "/etc/ld.so.cache",
    "/etc/ld.so.preload",
];

} // verus!
