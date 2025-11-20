use lexical_core::{write_with_options, NumberFormatBuilder};
use vstd::prelude::*;

use crate::{DekoPPtr, WellFormed};

// Remove the generic implementation and use a macro instead
macro_rules! impl_deko_debug_integer {
    ($($ty:ty),* $(,)?) => {
        $(
            verus! {

            impl DekoDebug for $ty {
                #[verifier::external_body]
                fn deko_debug<W: DekoWriter>(&self, writer: &W) {
                    let mut buffer = itoa::Buffer::new();
                    let s = buffer.format(*self);
                    writer.write_str(s);
                }

                #[verifier::external_body]
                fn deko_debug_hex<W: DekoWriter>(&self, writer: &W) {
                    print_integer_hex(*self, writer);
                }

                #[verifier::external_body]
                fn deko_debug_oct<W: DekoWriter>(&self, writer: &W) {
                    print_integer_oct(*self, writer);
                }
            }

            }
        )*
    };
}

macro_rules! debug_packed_field {
    ($self:expr, $field:ident, $method:ident) => {
        let value = $self.$field;
        value.$method();
    };
}

verus! {

/// Writer trait for custom formatting output.
pub trait DekoWriter {
    fn write_str(&self, s: &str);

    #[verifier::external_body]
    fn write_char(&self, c: char) {
        let mut buf = [0u8; 4];
        let s = c.encode_utf8(&mut buf);
        self.write_str(s);
    }

    #[verifier::external_body]
    fn write_bytes(&self, bytes: &[u8]) {
        for &b in bytes {
            self.write_char(b as char);
        }
    }
}

/// Custom debug trait for Verus-compatible debugging `without` heap allocation.
///
/// It is important to note that in Deko, one should always use heap-free formatting
/// (i.e., no [`alloc::string::String`] or [`alloc::format!`]) within the kernel or
/// low-level components. The primary reason is that heap objects are implicitly
/// allocated through the global allocator which we deliberately disable by panics.
///
/// Also [`vstd::vpanic!`] should be avoided as this will create a string for
/// [`core::fmt::Arguments`] which implicitly allocates on the heap as well. Thus,
/// if you call [`vstd::vpanic!`] inside the kernel, panic itself will panic, and
/// no meaningful panic information will be printed.
pub trait DekoDebug {
    /// Print debug information for this type
    fn deko_debug<W: DekoWriter>(&self, writer: &W);

    /// Print debug information in hexadecimal format.
    ///
    /// If the implementee does not have a specific hex format, this method
    /// will serve as the fallback to the normal debug format.
    fn deko_debug_hex<W: DekoWriter>(&self, writer: &W) {
       self.deko_debug(writer)
    }

    /// Print debug information in octal format.
    ///
    /// If the implementee does not have a specific octal format, this method
    /// will serve as the fallback to the normal debug format.
    fn deko_debug_oct<W: DekoWriter>(&self, writer: &W) {
        self.deko_debug(writer)
    }
}

#[verifier::external]
fn print_byte_hex_padded<W: DekoWriter>(byte: u8, writer: &W) {
    let hex_chars = b"0123456789ABCDEF";
    writer.write_char(hex_chars[(byte >> 4) as usize] as char);
    writer.write_char(hex_chars[(byte & 0xF) as usize] as char);
}

// Specific helpers for common cases with optimized buffer sizes
#[verifier::external]
pub(crate) fn print_integer_hex<T: lexical_core::ToLexicalWithOptions, W: DekoWriter>(num: T, writer: &W) {
    writer.write_str("0x");

    const FORMAT: u128 = NumberFormatBuilder::hexadecimal();
    let mut buffer = [0u8; 32]; // Enough for 128-bit hex
    let digits = write_with_options::<_, { FORMAT }>(
        num,
        &mut buffer,
        &T::Options::default(),
    );

    writer.write_bytes(&digits);
}

#[verifier::external]
pub(crate) fn print_integer_oct<T: lexical_core::ToLexicalWithOptions, W: DekoWriter>(num: T, writer: &W) {
    writer.write_str("0o");

    const FORMAT: u128 = NumberFormatBuilder::octal();
    let mut buffer = [0u8; 44]; // Enough for 128-bit octal
    let digits = write_with_options::<_, { FORMAT }>(
        num,
        &mut buffer,
        &T::Options::default(),
    );

    writer.write_bytes(&digits);
}

#[verifier::external]
pub(crate) fn print_integer_bin<T: lexical_core::ToLexicalWithOptions, W: DekoWriter>(num: T, writer: &W) {
    writer.write_str("0b");
    const FORMAT: u128 = NumberFormatBuilder::binary();
    let mut buffer = [0u8; 128]; // Enough for 128-bit
    let digits = write_with_options::<_, { FORMAT }>(
        num,
        &mut buffer,
        &T::Options::default(),
    );

    writer.write_bytes(&digits);
}


// Enhanced byte formatting using lexical
#[verifier::external_body]
pub(crate) fn print_byte_hex<W: DekoWriter>(byte: u8, writer: &W) {
    let mut buffer = [0u8; 2];

    const FORMAT: u128 = NumberFormatBuilder::hexadecimal();
    let digits = write_with_options::<_, { FORMAT }>(
        byte,
        &mut buffer,
        &Default::default(),
    );

    writer.write_bytes(&digits);
}

#[verifier::external_body]
pub(crate) fn print_offset_hex<W: DekoWriter>(offset: usize, writer: &W) {
    let mut buffer = [0u8; 16]; // Enough for 64-bit hex

    const FORMAT: u128 = NumberFormatBuilder::hexadecimal();
    let digits = write_with_options::<_, { FORMAT }>(
        offset,
        &mut buffer,
        &Default::default(),
    );

    writer.write_bytes(&digits);
}

#[verifier::external_body]
pub(crate) fn print_hex_dump_readable<W: DekoWriter>(bytes: &[u8], start_offset: usize, writer: &W) {
    if bytes.is_empty() {
        writer.write_str("(empty)\n");
        return;
    }

    const BYTES_PER_LINE: usize = 16;

    // Print header
    writer.write_str("         00 01 02 03 04 05 06 07  08 09 0A 0B 0C 0D 0E 0F  |ASCII           |\n");
    writer.write_str("       +────────────────────────────────────────────────+──+────────────────+\n");

    for (line_idx, chunk) in bytes.chunks(BYTES_PER_LINE).enumerate() {
        let offset = start_offset + (line_idx * BYTES_PER_LINE);

        // Print offset with consistent width
        print_offset_padded(offset, writer);
        writer.write_str(" │ ");

        // Print hex bytes in two groups of 8
        for (i, &byte) in chunk.iter().enumerate() {
            if i == 8 {
                writer.write_str(" "); // Extra space between groups
            }
            print_byte_hex_padded(byte, writer);
            writer.write_str(" ");
        }

        // Pad incomplete lines
        let padding_needed = BYTES_PER_LINE - chunk.len();
        for i in 0..padding_needed {
            if chunk.len() + i == 8 {
                writer.write_str(" "); // Maintain group spacing
            }
            writer.write_str("   "); // 3 spaces (2 hex + 1 space)
        }

        writer.write_str(" │");

        // Print ASCII with visual clarity
        for &byte in chunk.iter() {
            let c = match byte {
                0x00..=0x1F => '·',           // Control chars as middle dot
                0x20..=0x7E => byte as char,   // Printable ASCII
                0x7F => '⌂',                  // DEL as house symbol
                0x80..=0xFF => '▒',           // Extended ASCII as block
            };
            writer.write_char(c);
        }

        // Pad ASCII section for incomplete lines
        for _ in 0..padding_needed {
            writer.write_char(' ');
        }

        writer.write_str("│\n");
    }

    // Print footer
    writer.write_str("       +────────────────────────────────────────────────+──+────────────────+\n");
}

#[verifier::external_body]
fn print_offset_padded<W: DekoWriter>(offset: usize, writer: &W) {
    // Print 6-digit hex offset with leading zeros
    let mut buffer = [b'0'; 6];
    let mut temp = offset;
    let hex_chars = b"0123456789ABCDEF";

    for i in (0..6).rev() {
        buffer[i] = hex_chars[temp & 0xF];
        temp >>= 4;
    }

    for &b in buffer.iter() {
        writer.write_char(b as char);
    }
}

// Implement for all integer types explicitly
impl_deko_debug_integer!(
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
);

impl DekoDebug for bool {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str(if *self { "true" } else { "false" });
    }
}

impl DekoDebug for char {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_char(*self);
    }
}

impl DekoDebug for &str {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str(self);
    }
}

impl<T> DekoDebug for *const T {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        (*self as usize).deko_debug(writer);
    }
}

impl<T> DekoDebug for *mut T {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        (*self as usize).deko_debug(writer);
    }
}

impl<T: DekoDebug> DekoDebug for Option<T> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        match self {
            Some(ref inner) => {
                writer.write_str("Some(");
                inner.deko_debug(writer);
                writer.write_char(')');
            }
            None => writer.write_str("None"),
        }
    }
}

impl<T: DekoDebug, E: DekoDebug> DekoDebug for Result<T, E> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        match self {
            Ok(ref inner) => {
                writer.write_str("Ok(");
                inner.deko_debug(writer);
                writer.write_char(')');
            }
            Err(ref inner) => {
                writer.write_str("Err(");
                inner.deko_debug(writer);
                writer.write_char(')');
            }
        }
    }
}

// Blanket implementation for references - this allows &T to implement DekoDebug when T does
impl<T: DekoDebug + ?Sized> DekoDebug for &T {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        (*self).deko_debug(writer);
    }

    #[verifier::external_body]
    fn deko_debug_hex<W: DekoWriter>(&self, writer: &W) {
        (*self).deko_debug_hex(writer);
    }

    #[verifier::external_body]
    fn deko_debug_oct<W: DekoWriter>(&self, writer: &W) {
        (*self).deko_debug_oct(writer);
    }
}

impl<'a> DekoDebug for &'a [u8] {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        if self.is_empty() {
            writer.write_str("&[u8] { len: 0, data: [] }");
            return;
        }

        match self.len() {
            1..=8 => {
                // Very short - inline with brackets
                writer.write_str("&[u8] { len: ");
                self.len().deko_debug(writer);
                writer.write_str(", data: [");
                for (i, &byte) in self.iter().enumerate() {
                    if i > 0 { writer.write_str(", "); }
                    writer.write_str("0x");
                    print_byte_hex_padded(byte, writer);
                }
                writer.write_str("] }");
            }
            9..=32 => {
                // Short - compact hex line
                writer.write_str("&[u8] { len: ");
                self.len().deko_debug(writer);
                writer.write_str(", data:\n  ");

                for (i, &byte) in self.iter().enumerate() {
                    if i > 0 && i % 8 == 0 {
                        writer.write_str("\n  ");
                    } else if i > 0 {
                        writer.write_str(" ");
                    }

                    writer.write_str("0x");
                    print_byte_hex_padded(byte, writer);
                }
                writer.write_str("\n}");
            }
            _ => {
                // Long - full hex dump
                writer.write_str("&[u8] { len: ");
                self.len().deko_debug(writer);
                writer.write_str(", data:\n");
                print_hex_dump_readable(self, 0, writer);
                writer.write_str("}");
            }
        }
    }
}


impl<T: DekoDebug> DekoDebug for core::ops::Range<T> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        "Range { start: ".deko_debug(writer);
        self.start.deko_debug(writer);
        ", end: ".deko_debug(writer);
        self.end.deko_debug(writer);
        " }".deko_debug(writer);
    }
}

impl<T: DekoDebug + WellFormed, const N: usize> DekoDebug for deko_std::array::Array<T, N> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str("Array[");
        self.0.deko_debug(writer);
        writer.write_str("]");
    }
}

impl<T: DekoDebug, const N: usize> DekoDebug for [T; N] {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str("[");
        for i in 0..N {
            if i > 0 {
                writer.write_str(", ");
            }
            self[i].deko_debug(writer);
        }
        writer.write_str("]");
    }
}

impl<V: WellFormed> DekoDebug for DekoPPtr<V> {
    #[verifier::external_body]
    fn deko_debug<W: DekoWriter>(&self, writer: &W) {
        writer.write_str("DekoPPtr(");
        (self.addr()).deko_debug_hex(writer);
        writer.write_str(")");
    }
}

} // verus!
