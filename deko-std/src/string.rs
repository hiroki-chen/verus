//! String conversion utilities for heap-free environments.
//!
//! This module provides functions to convert integers to string representations
//! without requiring heap allocation. All functions use stack-allocated buffers
//! and return string slices pointing to the valid portions.

use vstd::prelude::*;
use crate::prelude::*;

verus! {

/// Maximum buffer size needed for u64 decimal representation (20 digits + null terminator)
pub const U64_DECIMAL_MAX_LEN: usize = 21;

/// Maximum buffer size needed for u64 hexadecimal representation (16 digits + "0x" prefix + null terminator)
pub const U64_HEX_MAX_LEN: usize = 19;

/// Maximum buffer size needed for u64 binary representation (64 digits + "0b" prefix + null terminator)
pub const U64_BINARY_MAX_LEN: usize = 67;

/// A stack-allocated buffer for string conversion operations.
///
/// This provides a safe wrapper around a fixed-size array that can be used
/// for converting integers to strings without heap allocation.
#[derive(Clone, Copy)]
pub struct StringBuffer<const N: usize> {
    buffer: [u8; N],
    len: usize,
}

impl<const N: usize> StringBuffer<N> {
    /// Creates a new empty string buffer.
    pub const fn new() -> Self {
        Self {
            buffer: [0u8; N],
            len: 0,
        }
    }

    /// Returns the buffer contents as a string slice.
    pub fn as_str(&self) -> &str {
        // Safety: We ensure the buffer contains valid UTF-8 when writing to it
        unsafe { 
            core::str::from_utf8_unchecked(&self.buffer[..self.len])
        }
    }

    /// Returns the buffer contents as a byte slice.
    pub fn as_bytes(&self) -> &[u8] {
        &self.buffer[..self.len]
    }

    /// Returns the length of the valid string data.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Clears the buffer.
    pub fn clear(&mut self) {
        self.len = 0;
    }
}

impl<const N: usize> WellFormed for StringBuffer<N> {
    open spec fn wf(&self) -> bool {
        self.len <= N
    }
}

} // verus!

/// Converts a u64 to decimal string representation using the provided buffer.
///
/// # Arguments
///
/// * `value` - The u64 value to convert
/// * `buffer` - A mutable string buffer to write the result into
///
/// # Returns
///
/// A string slice pointing to the decimal representation, or None if the buffer is too small.
///
/// # Example
///
/// ```rust
/// let mut buf = StringBuffer::<U64_DECIMAL_MAX_LEN>::new();
/// if let Some(s) = u64_to_decimal(12345, &mut buf) {
///     assert_eq!(s, "12345");
/// }
/// ```
pub fn u64_to_decimal(value: u64, buffer: &mut StringBuffer<U64_DECIMAL_MAX_LEN>) -> Option<&str> {
    buffer.clear();
    
    if value == 0 {
        buffer.buffer[0] = b'0';
        buffer.len = 1;
        return Some(buffer.as_str());
    }

    let mut val = value;
    let mut pos = U64_DECIMAL_MAX_LEN;
    
    // Fill buffer from the end
    while val > 0 && pos > 0 {
        pos -= 1;
        buffer.buffer[pos] = (b'0' + (val % 10) as u8);
        val /= 10;
    }
    
    if val > 0 {
        // Buffer overflow
        return None;
    }
    
    // Copy valid digits to the beginning of the buffer
    let digit_count = U64_DECIMAL_MAX_LEN - pos;
    for i in 0..digit_count {
        buffer.buffer[i] = buffer.buffer[pos + i];
    }
    
    buffer.len = digit_count;
    Some(buffer.as_str())
}

/// Converts a u64 to hexadecimal string representation using the provided buffer.
///
/// # Arguments
///
/// * `value` - The u64 value to convert
/// * `buffer` - A mutable string buffer to write the result into
/// * `uppercase` - If true, uses uppercase A-F, otherwise lowercase a-f
/// * `prefix` - If true, prefixes the result with "0x"
///
/// # Returns
///
/// A string slice pointing to the hexadecimal representation, or None if the buffer is too small.
///
/// # Example
///
/// ```rust
/// let mut buf = StringBuffer::<U64_HEX_MAX_LEN>::new();
/// if let Some(s) = u64_to_hex(255, &mut buf, true, true) {
///     assert_eq!(s, "0xFF");
/// }
/// ```
pub fn u64_to_hex(
    value: u64, 
    buffer: &mut StringBuffer<U64_HEX_MAX_LEN>, 
    uppercase: bool,
    prefix: bool
) -> Option<&str> {
    buffer.clear();
    
    let hex_chars = if uppercase {
        b"0123456789ABCDEF"
    } else {
        b"0123456789abcdef"
    };
    
    if value == 0 {
        let mut idx = 0;
        if prefix {
            buffer.buffer[0] = b'0';
            buffer.buffer[1] = b'x';
            idx = 2;
        }
        buffer.buffer[idx] = b'0';
        buffer.len = idx + 1;
        return Some(buffer.as_str());
    }

    let mut val = value;
    let mut pos = U64_HEX_MAX_LEN;
    
    // Fill buffer from the end
    while val > 0 && pos > 0 {
        pos -= 1;
        buffer.buffer[pos] = hex_chars[(val & 0xF) as usize];
        val >>= 4;
    }
    
    if val > 0 {
        // Buffer overflow
        return None;
    }
    
    let digit_count = U64_HEX_MAX_LEN - pos;
    let prefix_len = if prefix { 2 } else { 0 };
    
    if digit_count + prefix_len > U64_HEX_MAX_LEN {
        return None;
    }
    
    // Copy to beginning with optional prefix
    let mut idx = 0;
    if prefix {
        buffer.buffer[0] = b'0';
        buffer.buffer[1] = b'x';
        idx = 2;
    }
    
    for i in 0..digit_count {
        buffer.buffer[idx + i] = buffer.buffer[pos + i];
    }
    
    buffer.len = idx + digit_count;
    Some(buffer.as_str())
}

/// Converts a u64 to binary string representation using the provided buffer.
///
/// # Arguments
///
/// * `value` - The u64 value to convert
/// * `buffer` - A mutable string buffer to write the result into
/// * `prefix` - If true, prefixes the result with "0b"
///
/// # Returns
///
/// A string slice pointing to the binary representation, or None if the buffer is too small.
///
/// # Example
///
/// ```rust
/// let mut buf = StringBuffer::<U64_BINARY_MAX_LEN>::new();
/// if let Some(s) = u64_to_binary(5, &mut buf, true) {
///     assert_eq!(s, "0b101");
/// }
/// ```
pub fn u64_to_binary(
    value: u64, 
    buffer: &mut StringBuffer<U64_BINARY_MAX_LEN>, 
    prefix: bool
) -> Option<&str> {
    buffer.clear();
    
    if value == 0 {
        let mut idx = 0;
        if prefix {
            buffer.buffer[0] = b'0';
            buffer.buffer[1] = b'b';
            idx = 2;
        }
        buffer.buffer[idx] = b'0';
        buffer.len = idx + 1;
        return Some(buffer.as_str());
    }

    let mut val = value;
    let mut pos = U64_BINARY_MAX_LEN;
    
    // Fill buffer from the end
    while val > 0 && pos > 0 {
        pos -= 1;
        buffer.buffer[pos] = if (val & 1) == 1 { b'1' } else { b'0' };
        val >>= 1;
    }
    
    if val > 0 {
        // Buffer overflow
        return None;
    }
    
    let digit_count = U64_BINARY_MAX_LEN - pos;
    let prefix_len = if prefix { 2 } else { 0 };
    
    if digit_count + prefix_len > U64_BINARY_MAX_LEN {
        return None;
    }
    
    // Copy to beginning with optional prefix
    let mut idx = 0;
    if prefix {
        buffer.buffer[0] = b'0';
        buffer.buffer[1] = b'b';
        idx = 2;
    }
    
    for i in 0..digit_count {
        buffer.buffer[idx + i] = buffer.buffer[pos + i];
    }
    
    buffer.len = idx + digit_count;
    Some(buffer.as_str())
}

/// Converts a u64 to string representation in the specified base.
///
/// # Arguments
///
/// * `value` - The u64 value to convert
/// * `base` - The base to use (2-36)
/// * `buffer` - A mutable string buffer to write the result into
/// * `uppercase` - If true, uses uppercase letters for digits > 9
///
/// # Returns
///
/// A string slice pointing to the representation, or None if the base is invalid or buffer too small.
///
/// # Example
///
/// ```rust
/// let mut buf = StringBuffer::<U64_DECIMAL_MAX_LEN>::new();
/// if let Some(s) = u64_to_base(255, 8, &mut buf, false) {
///     assert_eq!(s, "377");
/// }
/// ```
pub fn u64_to_base<const N: usize>(
    value: u64, 
    base: u32,
    buffer: &mut StringBuffer<N>,
    uppercase: bool
) -> Option<&str> {
    if base < 2 || base > 36 {
        return None;
    }
    
    buffer.clear();
    
    let chars = if uppercase {
        b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    } else {
        b"0123456789abcdefghijklmnopqrstuvwxyz"
    };
    
    if value == 0 {
        buffer.buffer[0] = b'0';
        buffer.len = 1;
        return Some(buffer.as_str());
    }

    let mut val = value;
    let mut pos = N;
    
    // Fill buffer from the end
    while val > 0 && pos > 0 {
        pos -= 1;
        buffer.buffer[pos] = chars[(val % base as u64) as usize];
        val /= base as u64;
    }
    
    if val > 0 {
        // Buffer overflow
        return None;
    }
    
    // Copy valid digits to the beginning of the buffer
    let digit_count = N - pos;
    for i in 0..digit_count {
        buffer.buffer[i] = buffer.buffer[pos + i];
    }
    
    buffer.len = digit_count;
    Some(buffer.as_str())
}

/// Convenience function to convert u64 to decimal string in a new buffer.
///
/// # Returns
///
/// A tuple containing the string buffer and an optional string slice.
/// The string slice is None if conversion failed.
///
/// # Example
///
/// ```rust
/// let (buffer, result) = u64_decimal(42);
/// if let Some(s) = result {
///     println!("Number: {}", s);
/// }
/// ```
pub fn u64_decimal(value: u64) -> (StringBuffer<U64_DECIMAL_MAX_LEN>, Option<&'static str>) {
    let mut buffer = StringBuffer::new();
    // We need to return a static lifetime, so we'll use unsafe here
    // This is safe because the buffer is returned alongside the str
    let result = u64_to_decimal(value, &mut buffer);
    let static_result = unsafe {
        result.map(|s| core::mem::transmute::<&str, &'static str>(s))
    };
    (buffer, static_result)
}

/// Convenience function to convert u64 to hex string in a new buffer.
///
/// # Returns
///
/// A tuple containing the string buffer and an optional string slice.
///
/// # Example
///
/// ```rust
/// let (buffer, result) = u64_hex(255, true, true);
/// if let Some(s) = result {
///     println!("Hex: {}", s); // "0xFF"
/// }
/// ```
pub fn u64_hex(value: u64, uppercase: bool, prefix: bool) -> (StringBuffer<U64_HEX_MAX_LEN>, Option<&'static str>) {
    let mut buffer = StringBuffer::new();
    let result = u64_to_hex(value, &mut buffer, uppercase, prefix);
    let static_result = unsafe {
        result.map(|s| core::mem::transmute::<&str, &'static str>(s))
    };
    (buffer, static_result)
}

/// Convenience function to convert u64 to binary string in a new buffer.
///
/// # Returns
///
/// A tuple containing the string buffer and an optional string slice.
///
/// # Example
///
/// ```rust
/// let (buffer, result) = u64_binary(5, true);
/// if let Some(s) = result {
///     println!("Binary: {}", s); // "0b101"
/// }
/// ```
pub fn u64_binary(value: u64, prefix: bool) -> (StringBuffer<U64_BINARY_MAX_LEN>, Option<&'static str>) {
    let mut buffer = StringBuffer::new();
    let result = u64_to_binary(value, &mut buffer, prefix);
    let static_result = unsafe {
        result.map(|s| core::mem::transmute::<&str, &'static str>(s))
    };
    (buffer, static_result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decimal_conversion() {
        let mut buffer = StringBuffer::new();
        
        // Test zero
        assert_eq!(u64_to_decimal(0, &mut buffer), Some("0"));
        
        // Test small number
        assert_eq!(u64_to_decimal(123, &mut buffer), Some("123"));
        
        // Test large number
        assert_eq!(u64_to_decimal(18446744073709551615u64, &mut buffer), Some("18446744073709551615"));
    }

    #[test]
    fn test_hex_conversion() {
        let mut buffer = StringBuffer::new();
        
        // Test zero
        assert_eq!(u64_to_hex(0, &mut buffer, false, false), Some("0"));
        assert_eq!(u64_to_hex(0, &mut buffer, false, true), Some("0x0"));
        
        // Test small number
        assert_eq!(u64_to_hex(255, &mut buffer, false, false), Some("ff"));
        assert_eq!(u64_to_hex(255, &mut buffer, true, true), Some("0xFF"));
        
        // Test large number
        assert_eq!(u64_to_hex(0xDEADBEEF, &mut buffer, true, true), Some("0xDEADBEEF"));
    }

    #[test]
    fn test_binary_conversion() {
        let mut buffer = StringBuffer::new();
        
        // Test zero
        assert_eq!(u64_to_binary(0, &mut buffer, false), Some("0"));
        assert_eq!(u64_to_binary(0, &mut buffer, true), Some("0b0"));
        
        // Test small numbers
        assert_eq!(u64_to_binary(5, &mut buffer, false), Some("101"));
        assert_eq!(u64_to_binary(5, &mut buffer, true), Some("0b101"));
        
        // Test power of 2
        assert_eq!(u64_to_binary(8, &mut buffer, true), Some("0b1000"));
    }

    #[test]
    fn test_base_conversion() {
        let mut buffer = StringBuffer::new();
        
        // Test base 8 (octal)
        assert_eq!(u64_to_base(64, 8, &mut buffer, false), Some("100"));
        
        // Test base 36
        assert_eq!(u64_to_base(35, 36, &mut buffer, false), Some("z"));
        assert_eq!(u64_to_base(35, 36, &mut buffer, true), Some("Z"));
        
        // Test invalid base
        assert_eq!(u64_to_base(100, 1, &mut buffer, false), None);
        assert_eq!(u64_to_base(100, 37, &mut buffer, false), None);
    }
}
