use core::arch::x86_64::_rdrand64_step;
use core::fmt::write;

use deko_std::fmt::{DekoDebug, DekoWriter};
use uuid::{Builder, Uuid};
use vstd::prelude::*;

use crate::{die, kinfo};

verus! {

pub assume_specification[ uuid::Builder::into_uuid ](_0: uuid::Builder) -> uuid::Uuid
;

pub assume_specification[ uuid::Builder::from_bytes ](_0: [u8; 16]) -> uuid::Builder
;

pub assume_specification[ uuid::Uuid::as_u64_pair ](_0: &uuid::Uuid) -> (u64, u64)
;

pub assume_specification[ uuid::Uuid::from_u64_pair ](_0: u64, _1: u64) -> uuid::Uuid
;

pub assume_specification[ core::arch::x86_64::_rdrand64_step ](_0: &mut u64) -> i32
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUuid(Uuid);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBuilder(uuid::Builder);

pub struct DekoHardwareRng;

#[verifier::external_body]
#[inline]
pub fn uuid_print(uuid: &Uuid) {
    use core::fmt::Write;

    let mut s = heapless::String::<128>::new();
    write!(&mut s, "{}", uuid).unwrap();
    kinfo!("UUID", s.as_str());
}

impl DekoHardwareRng {
    fn get_random_u64(&self) -> u64 {
        let mut val: u64 = 0;
        unsafe {
            for _ in 0..10 {
                if _rdrand64_step(&mut val) == 1 {
                    return val;
                }
            }
        }

        die("RDRAND failed to generate a random number");
    }
}

pub fn generate_secure_uuid() -> Uuid {
    let upper = DekoHardwareRng.get_random_u64();
    let lower = DekoHardwareRng.get_random_u64();

    let mut bytes = [0u8;16];

    for i in 0..8 {
        bytes[i] = ((upper >> (8 * (7 - i))) & 0xFF) as u8;
        bytes[8 + i] = ((lower >> (8 * (7 - i))) & 0xFF) as u8;
    }

    Builder::from_bytes(bytes).into_uuid()
}

} // verus!
