use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{Attribute, Data, DeriveInput, Field, Fields, Ident, Lit, Variant};

#[derive(Debug, Clone)]
enum FieldFormat {
    Default,
    Hex,
    Oct,
    Bin,
    Size,
    Enabled,
    Skip,
}

#[derive(Debug, Clone)]
struct FieldInfo {
    name: String,
    ident: Ident,
    format: FieldFormat,
}

pub fn generate_deko_debug_impl(input: &DeriveInput) -> Result<TokenStream2, syn::Error> {
    match &input.data {
        Data::Struct(data_struct) => generate_struct_impl(input, &data_struct.fields),
        Data::Enum(data_enum) => generate_enum_impl(input, &data_enum.variants),
        Data::Union(_) => {
            Err(syn::Error::new_spanned(input, "DekoDebug cannot be derived for unions"))
        }
    }
}

fn generate_struct_impl(input: &DeriveInput, fields: &Fields) -> Result<TokenStream2, syn::Error> {
    let name = &input.ident;
    let struct_name = name.to_string();

    // Extract generics for proper impl bounds
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    // Check if struct is packed
    let is_packed = is_struct_packed(&input.attrs);

    match fields {
        Fields::Named(fields) => {
            let field_implementations = parse_named_fields(&fields.named)?;
            let field_debug_calls = generate_field_debug_calls(&field_implementations, is_packed);

            Ok(quote! {
                ::vstd::prelude::verus! {
                    // Use fully-qualified paths to work from any crate
                    impl #impl_generics ::deko_std::fmt::DekoDebug for #name #ty_generics #where_clause {
                        #[verifier::external_body]
                        fn deko_debug<W: ::deko_std::fmt::DekoWriter>(&self, writer: &W) {
                            writer.write_str(#struct_name);
                            writer.write_str(" {\n");
                            #(#field_debug_calls)*
                            writer.write_str("}");
                        }
                    }
                }
            })
        }
        Fields::Unnamed(fields) => {
            let field_debug_calls = generate_tuple_field_debug_calls(&fields.unnamed)?;

            Ok(quote! {
                ::vstd::prelude::verus! {
                    impl #impl_generics ::deko_std::fmt::DekoDebug for #name #ty_generics #where_clause {
                        #[verifier::external_body]
                        fn deko_debug<W: ::deko_std::fmt::DekoWriter>(&self, writer: &W) {
                            writer.write_str(#struct_name);
                            writer.write_str("(");
                            #(#field_debug_calls)*
                            writer.write_str(")");
                        }
                    }
                }
            })
        }
        Fields::Unit => Ok(quote! {
            ::vstd::prelude::verus! {
                impl #impl_generics ::deko_std::fmt::DekoDebug for #name #ty_generics #where_clause {
                    #[verifier::external_body]
                    fn deko_debug<W: ::deko_std::fmt::DekoWriter>(&self, writer: &W) {
                        writer.write_str(#struct_name);
                    }
                }
            }
        }),
    }
}

fn generate_enum_impl(
    input: &DeriveInput,
    variants: &syn::punctuated::Punctuated<Variant, syn::token::Comma>,
) -> Result<TokenStream2, syn::Error> {
    let name = &input.ident;
    let enum_name = name.to_string();

    // Extract generics for proper impl bounds
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let variant_arms = variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            let variant_name_str = variant_name.to_string();

            match &variant.fields {
                Fields::Named(fields) => {
                    let field_names: Vec<&Ident> =
                        fields.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
                    let field_debug_calls: Vec<proc_macro2::TokenStream> = fields
                        .named
                        .iter()
                        .map(|field| {
                            let field_ident = field.ident.as_ref().unwrap();
                            let field_name = field_ident.to_string();
                            let format = parse_field_attributes(&field.attrs)
                                .unwrap_or(FieldFormat::Default);

                            match format {
                                FieldFormat::Skip => quote! {},
                                FieldFormat::Hex => quote! {
                                    writer.write_str("  ");
                                    writer.write_str(#field_name);
                                    writer.write_str(": ");
                                    #field_ident.deko_debug_hex(writer);
                                    writer.write_str(",\n");
                                },
                                FieldFormat::Oct => quote! {
                                    writer.write_str("  ");
                                    writer.write_str(#field_name);
                                    writer.write_str(": ");
                                    #field_ident.deko_debug_oct(writer);
                                    writer.write_str(",\n");
                                },
                                FieldFormat::Enabled => quote! {
                                    writer.write_str("  ");
                                    writer.write_str(#field_name);
                                    writer.write_str(": ");
                                    if *#field_ident {
                                        writer.write_str("enabled");
                                    } else {
                                        writer.write_str("disabled");
                                    }
                                    writer.write_str(",\n");
                                },
                                _ => quote! {
                                    writer.write_str("  ");
                                    writer.write_str(#field_name);
                                    writer.write_str(": ");
                                    #field_ident.deko_debug(writer);
                                    writer.write_str(",\n");
                                },
                            }
                        })
                        .collect();

                    quote! {
                        #name::#variant_name { #(#field_names),* } => {
                            writer.write_str(#enum_name);
                            writer.write_str("::");
                            writer.write_str(#variant_name_str);
                            writer.write_str(" {\n");
                            #(#field_debug_calls)*
                            writer.write_str("}");
                        }
                    }
                }
                Fields::Unnamed(fields) => {
                    let field_indices: Vec<usize> = (0..fields.unnamed.len()).collect();
                    let field_names: Vec<Ident> =
                        field_indices.iter().map(|i| format_ident!("field_{}", i)).collect();
                    let field_debug_calls: Vec<proc_macro2::TokenStream> = field_names
                        .iter()
                        .enumerate()
                        .map(|(i, field_name)| {
                            if i > 0 {
                                quote! {
                                    writer.write_str(", ");
                                    #field_name.deko_debug(writer);
                                }
                            } else {
                                quote! {
                                    #field_name.deko_debug(writer);
                                }
                            }
                        })
                        .collect();

                    quote! {
                        #name::#variant_name(#(#field_names),*) => {
                            writer.write_str(#enum_name);
                            writer.write_str("::");
                            writer.write_str(#variant_name_str);
                            writer.write_str("(");
                            #(#field_debug_calls)*
                            writer.write_str(")");
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        #name::#variant_name => {
                            writer.write_str(#enum_name);
                            writer.write_str("::");
                            writer.write_str(#variant_name_str);
                        }
                    }
                }
            }
        })
        .collect::<Vec<_>>();

    Ok(quote! {
        ::vstd::prelude::verus! {
            impl #impl_generics ::deko_std::fmt::DekoDebug for #name #ty_generics #where_clause {
                #[verifier::external_body]
                fn deko_debug<W: ::deko_std::fmt::DekoWriter>(&self, writer: &W) {
                    match self {
                        #(#variant_arms)*
                    }
                }
            }
        }
    })
}

fn parse_named_fields(
    fields: &syn::punctuated::Punctuated<Field, syn::token::Comma>,
) -> Result<Vec<FieldInfo>, syn::Error> {
    fields
        .iter()
        .map(|field| {
            let ident = field
                .ident
                .as_ref()
                .ok_or_else(|| syn::Error::new_spanned(field, "Expected named field"))?;

            let format = parse_field_attributes(&field.attrs)?;
            let name = extract_custom_name(&field.attrs)?.unwrap_or_else(|| ident.to_string());

            Ok(FieldInfo { name, ident: ident.clone(), format })
        })
        .collect()
}

fn is_struct_packed(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        if attr.path().is_ident("repr") {
            if let Ok(_) = attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("packed") {
                    return Err(syn::Error::new_spanned(&meta.path, "packed found"));
                }
                Ok(())
            }) {
                // If we get here, no error was thrown, so no "packed" found
                continue;
            } else {
                // An error was thrown, which means "packed" was found
                return true;
            }
        }
    }
    false
}

fn generate_field_debug_calls(
    fields: &[FieldInfo],
    is_packed: bool,
) -> Vec<proc_macro2::TokenStream> {
    fields
        .iter()
        .map(|field| {
            let field_ident = &field.ident;
            let field_name = &field.name;

            if is_packed {
                // For packed structs, avoid taking references to fields
                match field.format {
                    FieldFormat::Skip => quote! {},
                    FieldFormat::Hex => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        unsafe {
                            let field_ptr = ::core::ptr::addr_of!(self.#field_ident);
                            (*field_ptr).deko_debug_hex(writer);
                        }
                        writer.write_str(",\n");
                    },
                    FieldFormat::Oct => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        unsafe {
                            let field_ptr = ::core::ptr::addr_of!(self.#field_ident);
                            (*field_ptr).deko_debug_oct(writer);
                        }
                        writer.write_str(",\n");
                    },
                    FieldFormat::Bin => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        writer.write_str("0b");
                        unsafe {
                            let field_ptr = ::core::ptr::addr_of!(self.#field_ident);
                            (*field_ptr).deko_debug(writer);
                        }
                        writer.write_str(",\n");
                    },
                    FieldFormat::Size => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        writer.write_str("<packed field>");
                        writer.write_str(",\n");
                    },
                    FieldFormat::Enabled => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        unsafe {
                            let field_ptr = ::core::ptr::addr_of!(self.#field_ident);
                            if *field_ptr {
                                writer.write_str("enabled");
                            } else {
                                writer.write_str("disabled");
                            }
                        }
                        writer.write_str(",\n");
                    },
                    FieldFormat::Default => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        unsafe {
                            let field_ptr = ::core::ptr::addr_of!(self.#field_ident);
                            (*field_ptr).deko_debug(writer);
                        }
                        writer.write_str(",\n");
                    },
                }
            } else {
                // For regular structs, use normal field access
                match field.format {
                    FieldFormat::Skip => quote! {},
                    FieldFormat::Hex => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        self.#field_ident.deko_debug_hex(writer);
                        writer.write_str(",\n");
                    },
                    FieldFormat::Oct => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        self.#field_ident.deko_debug_oct(writer);
                        writer.write_str(",\n");
                    },
                    FieldFormat::Bin => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        writer.write_str("0b");
                        self.#field_ident.deko_debug(writer);
                        writer.write_str(",\n");
                    },
                    FieldFormat::Size => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        {
                            #[cfg(feature = "logging")]
                            {
                                let size_value = ::deko_std::misc::get_size_value(self.#field_ident);
                                let size_unit = ::deko_std::misc::format_size_bytes(self.#field_ident);
                                size_value.deko_debug(writer);
                                writer.write_str(" ");
                                writer.write_str(size_unit);
                            }
                            #[cfg(not(feature = "logging"))]
                            {
                                self.#field_ident.deko_debug(writer);
                            }
                        }
                        writer.write_str(",\n");
                    },
                    FieldFormat::Enabled => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        if self.#field_ident {
                            writer.write_str("enabled");
                        } else {
                            writer.write_str("disabled");
                        }
                        writer.write_str(",\n");
                    },
                    FieldFormat::Default => quote! {
                        writer.write_str("  ");
                        writer.write_str(#field_name);
                        writer.write_str(": ");
                        self.#field_ident.deko_debug(writer);
                        writer.write_str(",\n");
                    },
                }
            }
        })
        .collect()
}

fn generate_tuple_field_debug_calls(
    fields: &syn::punctuated::Punctuated<Field, syn::token::Comma>,
) -> Result<Vec<proc_macro2::TokenStream>, syn::Error> {
    fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let index = syn::Index::from(i);
            let format = parse_field_attributes(&field.attrs)?;

            let debug_call = match format {
                FieldFormat::Skip => return Ok(quote! {}),
                FieldFormat::Hex => quote! { self.#index.deko_debug_hex(writer); },
                FieldFormat::Oct => quote! { self.#index.deko_debug_oct(writer); },
                FieldFormat::Bin => quote! {
                    writer.write_str("0b");
                    self.#index.deko_debug(writer);
                },
                FieldFormat::Size => quote! {
                    #[cfg(feature = "logging")]
                    {
                        let size_value = ::deko_std::misc::get_size_value(self.#index);
                        let size_unit = ::deko_std::misc::format_size_bytes(self.#index);
                        size_value.deko_debug(writer);
                        writer.write_str(" ");
                        writer.write_str(size_unit);
                    }
                    #[cfg(not(feature = "logging"))]
                    {
                        self.#index.deko_debug(writer);
                    }
                },
                FieldFormat::Enabled => quote! {
                    if self.#index {
                        writer.write_str("enabled");
                    } else {
                        writer.write_str("disabled");
                    }
                },
                FieldFormat::Default => quote! { self.#index.deko_debug(writer); },
            };

            if i > 0 {
                Ok(quote! {
                    writer.write_str(", ");
                    #debug_call
                })
            } else {
                Ok(debug_call)
            }
        })
        .collect()
}

fn parse_field_attributes(attrs: &[Attribute]) -> Result<FieldFormat, syn::Error> {
    let mut format = FieldFormat::Default;

    for attr in attrs {
        if attr.path().is_ident("deko") {
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("hex") {
                    format = FieldFormat::Hex;
                } else if meta.path.is_ident("oct") {
                    format = FieldFormat::Oct;
                } else if meta.path.is_ident("bin") {
                    format = FieldFormat::Bin;
                } else if meta.path.is_ident("size") {
                    format = FieldFormat::Size;
                } else if meta.path.is_ident("enabled") {
                    format = FieldFormat::Enabled;
                } else if meta.path.is_ident("skip") {
                    format = FieldFormat::Skip;
                } else if meta.path.is_ident("name") {
                    // Skip name attribute here, handled in extract_custom_name
                    let _ = meta.value()?;
                    let _: Lit = meta.input.parse()?;
                }
                Ok(())
            })?;
        }
    }

    Ok(format)
}

fn extract_custom_name(attrs: &[Attribute]) -> Result<Option<String>, syn::Error> {
    let mut custom_name = None;

    for attr in attrs {
        if attr.path().is_ident("deko") {
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("name") {
                    let value = meta.value()?;
                    let lit: Lit = value.parse()?;
                    if let Lit::Str(lit_str) = lit {
                        custom_name = Some(lit_str.value());
                    }
                }
                Ok(())
            })?;
        }
    }

    Ok(custom_name)
}
