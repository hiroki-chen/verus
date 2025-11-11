use proc_macro::TokenStream;
use syn::{DeriveInput, parse_macro_input};

pub(crate) mod imp;

/// Derive macro for DekoDebug trait
///
/// Supports field-level attributes:
/// - `#[deko(hex)]` - Format as hexadecimal
/// - `#[deko(bin)]` - Format as binary  
/// - `#[deko(oct)]` - Format as octal
/// - `#[deko(size)]` - Format as size (bytes/KB/MB/GB)
/// - `#[deko(enabled)]` - Format boolean as enabled/disabled
/// - `#[deko(skip)]` - Skip this field
/// - `#[deko(name = "custom_name")]` - Use custom field name
///
/// Example:
/// ```rust
/// #[derive(DekoDebug)]
/// struct MyStruct {
///     #[deko(hex)]
///     address: u64,
///     #[deko(size)]  
///     length: usize,
///     #[deko(enabled)]
///     active: bool,
///     #[deko(skip)]
///     internal: u32,
///     #[deko(name = "custom")]
///     field: u16,
/// }
/// ```
#[proc_macro_derive(DekoDebug, attributes(deko))]
pub fn derive_deko_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    imp::generate_deko_debug_impl(&input).unwrap_or_else(|e| e.to_compile_error()).into()
}
