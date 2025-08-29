use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, Ident, LitInt, Token, Type};

struct BitVectorAssertions {
    var_name: Ident,
    ty: Type,
    values: Vec<LitInt>,
}

impl Parse for BitVectorAssertions {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse: var_name, Type, [0, 1, 2, 5, 6, 7, 8, 63]
        let var_name = input.parse::<Ident>()?;
        input.parse::<Token![,]>()?;
        let ty = input.parse::<Type>()?;
        input.parse::<Token![,]>()?;

        // Parse the array of values
        let content;
        syn::bracketed!(content in input);
        let mut values = Vec::new();
        while !content.is_empty() {
            values.push(content.parse::<LitInt>()?);
            if !content.is_empty() {
                content.parse::<Token![,]>()?;
            }
        }

        Ok(BitVectorAssertions { var_name, ty, values })
    }
}

pub fn assert_all_bits_set(input: TokenStream) -> TokenStream {
    let BitVectorAssertions { var_name, ty, values } =
        parse_macro_input!(input as BitVectorAssertions);

    // Build the OR pattern: ((1 as T) << v1) | ((1 as T) << v2) | ...
    let or_pattern = values
        .iter()
        .map(|v| {
            quote! { ((1 as #ty) << #v) }
        })
        .reduce(|acc, item| {
            quote! { #acc | #item }
        })
        .unwrap_or_else(|| quote! { 0 });

    // Generate an assertion for each bit
    let assertions = values.iter().map(|v| {
        quote! {
            assert((#var_name) & ((1 as #ty) << #v) != 0) by (bit_vector)
                requires
                    #var_name == #or_pattern;
        }
    });

    let output = quote! {
        #(#assertions)*
    };

    output.into()
}
