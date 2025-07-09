use proc_macro::TokenStream;
use quote::quote;
use syn_verus::spanned::Spanned;
use syn_verus::{AttributeArgs, Field, Ident, Lit, LitInt, NestedMeta, Type, parse_macro_input};

pub fn field_name_ty(
    field: &Field,
    i: usize,
    span: proc_macro2::Span,
) -> (proc_macro2::TokenStream, Type) {
    let field_name = match &field.ident {
        Some(name) => quote! {#name},
        None => {
            let lit = Lit::Int(LitInt::new(format!("{}", i).as_str(), span));
            quote! {#lit}
        }
    };

    (field_name, field.ty.clone())
}

pub fn bits(attribute: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as syn_verus::Item);
    // This is a placeholder implementation.
    // You can implement the actual logic for the `bits` macro here.
    // For now, we just return the item as is.
    let mut fields_stream = quote! {};
    let args = parse_macro_input!(attribute as AttributeArgs);
    let s = match &input {
        syn_verus::Item::Struct(s) => s,
        _ => panic!("Expected a struct item"),
    };

    let bitstruct = &args[0];
    let valuetype = &args[1];
    //println!("{} : {}\n", quote! {#bitstruct}, quote! {#valuetype});
    //let bitstruct = Ident::new(&attr.to_string(), s.span());
    let specname = &s.ident;
    let mut specfields = quote! {arbitrary::<#specname>()};
    let mut emptyspec = quote! {arbitrary::<#specname>()};
    let mut specstruct = quote! {};
    let mut max_bits = 0;

    for (i, field) in s.fields.iter().enumerate() {
        let (fname, fty) = field_name_ty(&field, i, s.span());
        let setter = Ident::new(&format!("set_{}", fname), fname.span());
        let getter: Ident = Ident::new(&format!("get_{}", fname), fname.span());
        let bound_getter: Ident = Ident::new(&format!("lemma_bound_{}", fname), fname.span());

        let spec_setter = Ident::new(&format!("spec_set_{}", fname), fname.span());
        let spec_getter = Ident::new(&format!("spec_{}", fname), fname.span());
        let mut bit_start: u64 = 0;
        let mut bit_last: u64 = 0;
        for attr in &field.attrs {
            let name = attr.path.get_ident();
            if name.unwrap().to_string() == "bit" {
                //bit_start = attr.path.segments[1];
                //bit_last = attr.path.segments[2];
                if let Result::Ok(meta) = attr.parse_meta() {
                    match meta {
                        syn_verus::Meta::Path(_) => todo!(),
                        syn_verus::Meta::List(metalist) => {
                            if let NestedMeta::Lit(Lit::Int(litint)) = &metalist.nested[0] {
                                bit_start = litint.base10_parse::<u64>().unwrap();
                                bit_last = bit_start;
                            }
                            if metalist.nested.len() >= 2 {
                                if let NestedMeta::Lit(Lit::Int(litint)) = &metalist.nested[1] {
                                    bit_last = litint.base10_parse::<u64>().unwrap();
                                }
                            }
                        }
                        syn_verus::Meta::NameValue(_) => todo!(),
                    }
                }
            }
        }

        max_bits = if max_bits < bit_last { bit_last } else { max_bits };
        let field_max_val: u64 = (1 << (bit_last - bit_start + 1)) - 1;
        let mask: u64 = field_max_val;
        let set_mask: u64 = field_max_val << bit_start;

        fields_stream = quote! {
            #fields_stream
            verus!{
            #[inline(always)]
            pub const fn #setter(&self, val: #fty) -> (ret: Self)
            requires
                val <= #field_max_val as #fty
            ensures
                builtin::equal(ret.view(), self.view().#spec_setter(val))
            {
                let mask = #set_mask as #fty;
                let value = self.value();
                let ghost oldv = value;
                let value = (value & (!mask)) | (val << (#bit_start as #fty));
                let ret = #bitstruct{value};
                proof {
                    let actual_ret = ret.view();
                    let expected_ret = self.view().#spec_setter(val);
                    assume(builtin::equal(actual_ret, expected_ret));
                }
                ret
            }}

            verus!{
            pub proof fn #bound_getter(&self) -> (ret: #fty)
            ensures
                ret == self.#spec_getter(),
                ret <= #field_max_val as #fty,
                ret >= 0,
            {
                bit64_and_auto();
                self.#spec_getter()
            }

            pub const fn #getter(&self) -> (ret: #fty)
            ensures
                ret == self.view().#spec_getter(),
                self.view().#spec_getter() <= #field_max_val as #fty
            {
                proof {
                    bit64_and_auto();
                }
                let mask = #mask as #fty;
                (self.value() >> (#bit_start as #fty)) & mask
            }
            }

            verus!{
            pub open spec fn #spec_getter(&self) -> #fty {
                let mask = #mask as #fty;
                (self.value as #fty >> (#bit_start as #fty)) & mask
            }
            }
        };

        specfields = quote! {
            #specfields.#spec_setter(self.#spec_getter() as #fty)
        };
        emptyspec = quote! {
            #emptyspec.#spec_setter(0)
        };
        let vis = &field.vis;
        specstruct = quote! {
            #specstruct
            #vis #fname: #fty,
        };
    }
    let vis = &s.vis;
    let max_val: u128 = (1 << max_bits) - 1;
    //println!("max_val = {} max_bits ={}", max_val, max_bits);
    let expanded = quote! {
        verus!{
        // #[derive(SpecGetter, SpecSetter)]
        #vis ghost struct #specname {
            #specstruct
        }
        }
        verus!{
        impl #specname {
            pub open spec fn empty() -> #specname {
                #emptyspec
            }

            pub open spec fn new(val: #valuetype) -> #specname;

            #[verifier(external_body)]
            pub broadcast proof fn axiom_new(val: #bitstruct)
            ensures
                builtin::equal(#[trigger]Self::new(val.value), #[trigger]val.view())
            {}

            pub open spec fn to_value(&self) -> #bitstruct;

            #[verifier(external_body)]
            pub broadcast proof fn axiom_into(self)
            ensures
                builtin::equal(#[trigger]self.to_value()@, self),
            {}
            }
        }

        verus!{
        // #[derive(Copy, PartialEq, Eq, Structural, ExecStruct, NotPrimitive, SpecSize, VSpecEq, IsConstant, WellFormed)]
        #[derive(Copy, Clone, PartialEq, Eq, Default)]
        #[repr(C, align(1))]
        pub struct #bitstruct {
            pub value: #valuetype,
        }
        }
        verus!{
        impl Clone for #bitstruct {
            #[verifier(external_body)]
            fn clone(&self) -> (ret: Self)
            ensures
                builtin::equal(*self, ret),
            {
                #bitstruct { value: self.value }
            }
        }
        }


        verus!{
        impl #bitstruct {
            verus! {
                pub open spec fn inv(&self) -> bool {
                    0 <= (self.value as int) <= (#max_val as int)
                }

                #[verifier(external_body)]
                pub broadcast proof fn axiom_inv(&self)
                ensures
                    #[trigger] self.inv(),
                    0 <= (#[trigger]self.value as int) <= (#max_val as int)
                {}
            }

            verus! {
                pub const fn new(val: #valuetype) -> (ret: Self)
                ensures
                    builtin::equal(ret, Self::spec_new(val)),
                    builtin::equal(ret.view(), #specname::new(val)),
                {
                    #bitstruct { value:val}
                }

                pub open spec fn spec_new(val: #valuetype) -> (ret: Self) {
                    #bitstruct { value:val}
                }

                pub broadcast proof fn lemma_new_eq(self)
                ensures
                    builtin::equal(Self::spec_new(self.value), self)
                {}

                pub const fn empty() -> (ret: Self)
                ensures
                    builtin::equal(ret.view(), #specname::empty())
                {
                    let ret = #bitstruct { value: 0 };
                    proof{
                        let val = ret.value;
                        assert forall |mask: #valuetype, offset: #valuetype|
                            #[trigger]((val >> offset) & mask)  == 0 as #valuetype
                        by {
                            assert_bit_vector(val != 0 || ((val >> offset) & mask) == 0);
                        }
                    }
                    ret
                }
            }

            #fields_stream
            verus!{
            pub open spec fn view(&self) -> #specname {
                #specfields
            }
            }
            verus!{
            pub const fn value(&self) -> (ret: #valuetype)
            ensures
                equal(ret, self.value),
                self.value <= #max_val as #valuetype
            {
                proof{
                    assert(self.inv());
                }
                self.value
            }
            }
        }
    }
    };

    TokenStream::from(expanded)
}
