use proc_macro::TokenStream;

mod imp;

#[proc_macro]
pub fn assert_all_bits_set(input: TokenStream) -> TokenStream {
    imp::assert_all_bits_set(input)
}
