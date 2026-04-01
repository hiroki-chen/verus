use aes_gcm::{
    aead::{AeadInPlace, KeyInit}, // 引入 InPlace trait 以支持直接写入 buffer
    Aes256Gcm,
    Key,
    Nonce,
    Tag,
};
use vstd::prelude::*;

use crate::collections::update_slice;
use crate::cpu::rdrand64_step;
use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};

verus! {

/// Generates a new random AES-GCM-256 key.
#[verus_spec(
    requires
        old(key).len() == 32,
    ensures
        old(key)@.len() == final(key)@.len(),
)]
pub fn aes_gcm_256_key_gen(key: &mut [u8; 32]) {
    for i in 0..4 {
        let rand_bytes = rdrand64_step();

        for j in 0..8
            invariant
                rand_bytes@.len() == 8,
                0 <= i < 4,
                0 <= j <= 8,
                key@.len() == 32,
        {
            update_slice(key, i * 8 + j, rand_bytes[j]);
        }
    }
}

/// Encrypts the given plaintext using AES-GCM with the provided nonce and key,
/// writing the result into out_buf.
#[verus_spec(r =>
    requires
        nonce.len() == 12,
        key.len() == 32,
        old(out_buf)@.len() >= plaintext.len() + 16 /* auth tag. */,
    ensures
        old(out_buf)@.len() == final(out_buf)@.len(),
)]
#[verifier::external_body]
pub fn encrypt(
    nonce: &[u8],
    plaintext: &[u8],
    key: &[u8],
    out_buf: &mut [u8],
) -> DekoGuestServResult<()> {
    let aes_key = Key::<Aes256Gcm>::from_slice(key);

    let cipher = Aes256Gcm::new(aes_key);
    let nonce = Nonce::from_slice(nonce);  // 96-bits; unique per message
    let r = cipher.encrypt_in_place_detached(nonce, plaintext, out_buf).map_err(
        |_| DekoGuestServError::SoftError(DekoGuestServResultCode::Other(0x114514)),
    )?;

    // Append the auth tag at the end of the ciphertext
    out_buf[plaintext.len()..plaintext.len() + 16].copy_from_slice(&r);

    Ok(())
}

#[verus_spec(r =>
    requires
        nonce.len() == 12,
        ciphertext_with_tag.len() >= 16 /* auth tag. */,
        key.len() == 32,
        old(out_buf)@.len() >= ciphertext_with_tag.len() - 16,
    ensures
        old(out_buf)@.len() == final(out_buf)@.len(),
)]
#[verifier::external_body]
pub fn decrypt(
    nonce: &[u8],
    ciphertext_with_tag: &[u8],
    key: &[u8],
    out_buf: &mut [u8],
) -> DekoGuestServResult<()> {
    let aes_key = Key::<Aes256Gcm>::from_slice(key);
    let cipher = Aes256Gcm::new(aes_key);
    let nonce = Nonce::from_slice(nonce);  // 96-bits; unique
    let (ciphertext, tag) = ciphertext_with_tag.split_at(ciphertext_with_tag.len() - 16);
    let tag = Tag::from_slice(tag);
    cipher.decrypt_in_place_detached(nonce, ciphertext, out_buf, tag).map_err(
        |_| DekoGuestServError::SoftError(DekoGuestServResultCode::Other(0x114515)),
    )?;
    Ok(())
}

} // verus!
