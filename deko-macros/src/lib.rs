use proc_macro::TokenStream;

mod imp;

#[proc_macro_attribute]
pub fn bits(attribute: TokenStream, item: TokenStream) -> TokenStream { imp::bits(attribute, item) }
