use proc_macro::TokenStream;
use proc_macro2::{Group, TokenTree};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Ident, Result, Token, Type, parse_macro_input, parse_quote};

/// Represents the input to the with_atomic_pred macro
#[derive(Debug)]
pub struct AtomicPredInput {
    pub name: Ident,
    pub data_type: Type,
    pub perm_type: Type,
    pub data_fields: Option<Vec<Ident>>,
    pub perm_fields: Option<Vec<Ident>>,
    pub expressions: Option<Vec<TokenStream>>,
}

impl Parse for AtomicPredInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        let perm_type: Type = input.parse()?;

        // Use the name as both the predicate name and data type
        let data_type: Type = parse_quote! { #name };

        // Check if there's more content
        if input.is_empty() {
            return Ok(AtomicPredInput {
                name,
                data_type,
                perm_type,
                data_fields: None,
                perm_fields: None,
                expressions: None,
            });
        }

        input.parse::<Token![,]>()?;

        // Try to parse structured input with fields: and perm_fields:
        let mut perm_fields = None;
        let mut expressions = Vec::new();

        // Check for fields: declaration
        if input.peek(Ident) {
            if let Ok(keyword) = input.fork().parse::<Ident>() {
                if keyword == "fields" {
                    input.parse::<Ident>()?; // consume "fields"
                    input.parse::<Token![:]>()?;

                    let content;
                    let _brace = syn::braced!(content in input);
                    let field_list: Punctuated<Ident, Token![,]> =
                        content.parse_terminated(Ident::parse, Token![,])?;
                    let data_fields = Some(field_list.into_iter().collect());

                    input.parse::<Token![,]>()?;

                    // Parse perm_fields:
                    if input.peek(Ident) {
                        if let Ok(keyword) = input.fork().parse::<Ident>() {
                            if keyword == "perm_fields" {
                                input.parse::<Ident>()?; // consume "perm_fields"
                                input.parse::<Token![:]>()?;

                                let content;
                                let _brace = syn::braced!(content in input);
                                let perm_field_list: Punctuated<Ident, Token![,]> =
                                    content.parse_terminated(Ident::parse, Token![,])?;
                                perm_fields = Some(perm_field_list.into_iter().collect());

                                input.parse::<Token![,]>()?;
                            }
                        }
                    }

                    // Parse the remaining expression
                    if !input.is_empty() {
                        let remaining_tokens: proc_macro2::TokenStream = input.parse()?;
                        expressions.push(remaining_tokens.into());
                    }

                    return Ok(AtomicPredInput {
                        name,
                        data_type,
                        perm_type,
                        data_fields,
                        perm_fields,
                        expressions: if expressions.is_empty() { None } else { Some(expressions) },
                    });
                }
            }
        }

        // Fallback: parse everything as a single expression
        let remaining_tokens: proc_macro2::TokenStream = input.parse()?;
        let expressions = vec![remaining_tokens.into()];

        Ok(AtomicPredInput {
            name,
            data_type,
            perm_type,
            data_fields: None,
            perm_fields: None,
            expressions: Some(expressions),
        })
    }
}

/// Recursively replaces tokens in a token stream
fn replace_tokens_in_stream(
    tokens: TokenStream,
    data_fields: &[String],
    perm_fields: &[String],
) -> TokenStream {
    let tokens2: proc_macro2::TokenStream = tokens.into();
    let mut result = proc_macro2::TokenStream::new();

    for token in tokens2 {
        match token {
            TokenTree::Group(group) => {
                let delimiter = group.delimiter();
                let inner =
                    replace_tokens_in_stream(group.stream().into(), data_fields, perm_fields);
                let inner2: proc_macro2::TokenStream = inner.into();
                let new_group = Group::new(delimiter, inner2);
                result.extend(quote! { #new_group });
            }
            TokenTree::Ident(ident) => {
                let ident_str = ident.to_string();
                if perm_fields.contains(&ident_str) {
                    result.extend(quote! { v.perm@.#ident });
                } else if data_fields.contains(&ident_str) {
                    result.extend(quote! { v.data.#ident });
                } else {
                    // We allow directly accessing `data` and `perm`
                    if ident_str == "perm" {
                        result.extend(quote! { v.perm@ });
                    } else if ident_str == "data" {
                        result.extend(quote! { v.data });
                    } else {
                        result.extend(quote! { #ident });
                    }
                }
            }
            other => result.extend(quote! { #other }),
        }
    }

    result.into()
}

/// Generate the predicate implementation
pub fn generate_atomic_pred(input: AtomicPredInput) -> proc_macro2::TokenStream {
    let AtomicPredInput { name, data_type, perm_type, data_fields, perm_fields, expressions } =
        input;

    let pred_name = syn::Ident::new(&format!("{}Pred", name), name.span());
    let rw_impl = quote! {
        impl deko_std::prelude::RwLockPredicate<deko_std::sync::DekoAtomicData<#data_type, #perm_type>>
            for #pred_name
            {
                #[verifier::inline]
                open spec fn inv(self, v: deko_std::sync::DekoAtomicData<#data_type, #perm_type>) -> bool {
                    <Self as deko_std::prelude::Predicate<deko_std::sync::DekoAtomicData<#data_type, #perm_type>>>::inv(self, v)
                }
            }
    };

    // Default case: just return true
    if expressions.is_none()
        || expressions.as_ref().is_some_and(|tt| tt.is_empty() || tt.len() == 1 && tt[0].is_empty())
    {
        return quote! {
            verus! {
                pub struct #pred_name;

                impl deko_std::prelude::Predicate<deko_std::sync::DekoAtomicData<#data_type, #perm_type>> for #pred_name {
                    #[verifier::inline]
                    open spec fn inv(self, v: deko_std::sync::DekoAtomicData<#data_type, #perm_type>) -> bool {
                        true
                    }
                }

                #rw_impl
            }
        };
    }

    // For now, let's handle the case where expressions are provided as raw tokens
    let expressions = expressions.unwrap();

    // If we have field lists, do replacement
    let final_expressions = if let (Some(data_fields), Some(perm_fields)) =
        (data_fields, perm_fields)
    {
        let data_field_strings: Vec<String> = data_fields.iter().map(|i| i.to_string()).collect();
        let perm_field_strings: Vec<String> = perm_fields.iter().map(|i| i.to_string()).collect();

        expressions
            .into_iter()
            .map(|expr| replace_tokens_in_stream(expr, &data_field_strings, &perm_field_strings))
            .collect()
    } else {
        expressions
    };

    // Convert to proc_macro2::TokenStream and combine with &&&
    let combined_exprs: proc_macro2::TokenStream = if final_expressions.is_empty() {
        quote! { true }
    } else {
        final_expressions
            .into_iter()
            .map(|ts| -> proc_macro2::TokenStream { ts.into() })
            .reduce(|acc, expr| quote! { #acc &&& #expr })
            .unwrap_or_else(|| quote! { true })
    };

    quote! {
        verus! {
            pub struct #pred_name;

            impl deko_std::prelude::Predicate<deko_std::sync::DekoAtomicData<#data_type, #perm_type>> for #pred_name {
                #[verifier::inline]
                open spec fn inv(self, v: deko_std::sync::DekoAtomicData<#data_type, #perm_type>) -> bool {
                    #combined_exprs
                }
            }

            #rw_impl
        }
    }
}

/// The main macro implementation
pub fn with_atomic_pred_impl(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as AtomicPredInput);
    generate_atomic_pred(input).into()
}
