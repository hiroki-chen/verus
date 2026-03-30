use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

pub(crate) mod atomic_pred;
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
/// ```rust,norun
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

/// Macro for generating atomic predicates
///
/// Usage:
/// ```rust,norun
/// with_atomic_pred!(DekoRunnable, DekoRunnable, DekoRunnablePermission,
///     fields: { xsave },
///     perm_fields: { xsave_perm },
///     xsave_perm.pptr() == xsave@ &&& xsave_perm.is_init() &&& xsave_perm.wf()
/// );
/// ```
#[proc_macro]
pub fn with_atomic_pred(input: TokenStream) -> TokenStream {
    atomic_pred::with_atomic_pred_impl(input)
}

/// Procedural macro for constant declarations with spec and exec versions
///
/// Usage:
/// ```rust,norun
/// deko_const_decl!(pub, MY_CONST, u64, 0x1000);
/// ```
///
/// With documentation:
/// ```rust,norun
/// deko_const_decl!(
///     /// This is a constant used for memory alignment
///     /// It represents 4KB page size
///     pub, PAGE_SIZE, usize, 0x1000
/// );
/// ```
///
/// Generates:
/// ```rust,norun
/// verus! {
///     /// This is a constant used for memory alignment
///     /// It represents 4KB page size
///     pub spec const PAGE_SIZE_SPEC: usize = 0x1000;
///     /// This is a constant used for memory alignment
///     /// It represents 4KB page size
///     #[verifier::when_used_as_spec(PAGE_SIZE_SPEC)]
///     pub exec const PAGE_SIZE: usize
///         ensures
///             PAGE_SIZE == PAGE_SIZE_SPEC,
///         { 0x1000 }
/// }
/// ```
#[proc_macro]
pub fn deko_const_decl(input: TokenStream) -> TokenStream { deko_const_decl_impl(input) }

fn deko_const_decl_impl(input: TokenStream) -> TokenStream {
    use proc_macro2::TokenStream as TokenStream2;
    use quote::quote;
    use syn::parse::{Parse, ParseStream};
    use syn::{Attribute, Expr, Ident, Token, Type, Visibility};

    struct DekoConstDeclInput {
        attrs: Vec<Attribute>,
        vis: Visibility,
        name: Ident,
        ty: Type,
        spec_val: Expr,
        exec_val: Expr,
    }

    impl Parse for DekoConstDeclInput {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            // default to pub
            let vis: Visibility = match input.peek(Token![pub]) {
                true => {
                    let v = input.parse()?;
                    input.parse::<Token![,]>()?;
                    v
                }
                false => Visibility::Public(Token![pub](input.span())),
            };

            let attrs = input.call(syn::Attribute::parse_outer)?;
            let name = input.parse()?;
            input.parse::<Token![,]>()?;
            let ty = input.parse()?;
            input.parse::<Token![,]>()?;
            let spec_val = input.parse()?;
            input.parse::<Token![,]>()?;
            let exec_val = input.parse()?;

            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }

            Ok(DekoConstDeclInput { attrs, vis, name, ty, spec_val, exec_val })
        }
    }

    let parsed = syn::parse_macro_input!(input as DekoConstDeclInput);

    let attrs = &parsed.attrs;
    let vis = &parsed.vis;
    let name = &parsed.name;
    let ty = &parsed.ty;
    let spec_val = &parsed.spec_val;
    let val = &parsed.exec_val;

    // Create the spec constant name by appending _SPEC
    let spec_name = syn::Ident::new(&format!("{}_SPEC", name), name.span());

    let output: TokenStream2 = quote! {
        verus! {
            #(#attrs)*
            #vis spec const #spec_name : #ty = #spec_val;
            #(#attrs)*
            #[verifier::when_used_as_spec(#spec_name)]
            #vis exec const #name: #ty
                ensures
                    #name == #spec_name,
                { #val }
        }
    };

    output.into()
}
