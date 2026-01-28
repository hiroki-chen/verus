use sha3::Digest;
use vstd::prelude::*;

verus! {

#[verus_spec()]
#[verifier::external_body]
pub fn sha3_384_hash(data: &[u8]) -> [u8; 48] {
    let mut hasher = sha3::Sha3_384::new();
    hasher.update(data);
    let result = hasher.finalize();

    let mut hash = [0u8; 48];
    hash.copy_from_slice(&result[..48]);
    hash
}

} // verus!
