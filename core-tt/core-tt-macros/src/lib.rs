use {
    proc_macro::TokenStream,
    quote::{format_ident, quote},
    syn::{
        parse_macro_input, parse_quote,
        Attribute, Data, DataStruct, DeriveInput, Fields, Ident, WherePredicate,
    },
};

#[proc_macro_derive(Contextual, attributes(contextual))]
pub fn derive_contextual(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let DeriveInput { attrs: _, vis: _, ident, generics, data } = input;
    let output = match data {
        Data::Struct(data_struct) => {
            derive_contextual_struct(ident, generics, data_struct)
        },
        Data::Enum(data_enum) => {
            derive_contextual_enum(ident, generics, data_enum)
        },
        _ => panic!("derive(Contextual) can only be applied to structs and enums"),
    };

    output.into()
}

fn derive_contextual_struct(
    ident: syn::Ident,
    generics: syn::Generics,
    data_struct: syn::DataStruct,
) -> proc_macro2::TokenStream {
    let DataStruct { struct_token: _, fields, semi_token: _ } = data_struct;

    match fields {
        Fields::Named(fields) => {
            derive_contextual_struct_named(
                ident, generics, fields,
            )
        },
        Fields::Unnamed(fields) => {
            derive_contextual_struct_unnamed(
                ident, generics, fields,
            )
        },
        Fields::Unit => {
            derive_contextual_unit_struct(
                ident, generics,
            )
        },
    }
}

fn attributes_contain_ignore(attributes: &[Attribute]) -> bool {
    for attribute in attributes {
        let Some(ident) = attribute.path().get_ident() else {
            continue;
        };
        if ident != "contextual" {
            continue;
        }
        let args: Ident = attribute.parse_args().unwrap();
        if args != "ignore" {
            panic!("unrecognized argument in #[contextual(..)] attribute. Expected 'ignore'");
        }
        return true;
    }
    false
}

fn make_generic_where_clauses(
    generics: &mut syn::Generics,
) {
    let mut generic_where_clauses: Vec<WherePredicate> = Vec::new();
    for type_param in generics.type_params() {
        let ident = &type_param.ident;
        generic_where_clauses.push(parse_quote! {
            #ident: ::core_tt_simpler::Contextual
        });
    }
    if !generic_where_clauses.is_empty() {
        let where_clause = generics.make_where_clause();
        where_clause.predicates.extend(generic_where_clauses);
    }
}

fn derive_contextual_struct_named(
    ident: syn::Ident,
    mut generics: syn::Generics,
    fields: syn::FieldsNamed,
) -> proc_macro2::TokenStream {
    let field_names: Vec<_> = {
        fields
        .named
        .iter()
        .filter_map(|field| {
            if attributes_contain_ignore(&field.attrs) {
                None
            } else {
                Some(field.ident.as_ref().unwrap())
            }
        })
        .collect()
    };

    make_generic_where_clauses(&mut generics);
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        impl #impl_generics ::core_tt_simpler::Contextual for #ident #type_generics
        #where_clause
        {
            fn ctx_len(&self) -> usize {
                let mut ret = 0;
                #(
                    ret = ::core::cmp::max(
                        ret,
                        ::core_tt_simpler::Contextual::ctx_len(&self.#field_names),
                    );
                )*
                ret
            }

            fn collect_usages(&self, usages: &mut ::core_tt_simpler::Usages) {
                #(
                    ::core_tt_simpler::Contextual::collect_usages(&self.#field_names, usages);
                )*
            }

            fn filter_usages(&mut self, usages: &::core_tt_simpler::Usages) {
                #(
                    ::core_tt_simpler::Contextual::filter_usages(&mut self.#field_names, usages);
                )*
            }

            fn unfilter_usages(&mut self, usages: &::core_tt_simpler::Usages) {
                #(
                    ::core_tt_simpler::Contextual::unfilter_usages(&mut self.#field_names, usages);
                )*
            }
        }
    }
}

fn derive_contextual_struct_unnamed(
    ident: syn::Ident,
    mut generics: syn::Generics,
    fields: syn::FieldsUnnamed,
) -> proc_macro2::TokenStream {
    let pattern_field_names: Vec<_> = {
        fields
        .unnamed
        .iter()
        .enumerate()
        .map(|(index, field)| {
            if attributes_contain_ignore(&field.attrs) {
                Some(format_ident!("_field_{}", index))
            } else {
                Some(format_ident!("field_{}", index))
            }
        })
        .collect()
    };

    let field_names: Vec<_> = {
        fields
        .unnamed
        .iter()
        .enumerate()
        .filter_map(|(index, field)| {
            if attributes_contain_ignore(&field.attrs) {
                None
            } else {
                Some(format_ident!("field_{}", index))
            }
        })
        .collect()
    };

    make_generic_where_clauses(&mut generics);
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        impl #impl_generics ::core_tt_simpler::Contextual for #ident #type_generics
        #where_clause
        {
            fn ctx_len(&self) -> usize {
                let #ident(#(#pattern_field_names,)*) = self;
                let ret = 0;
                #(
                    let ret = ::core::cmp::max(
                        ret,
                        ::core_tt_simpler::Contextual::ctx_len(#field_names),
                    );
                )*
                ret
            }

            fn collect_usages(&self, usages: &mut ::core_tt_simpler::Usages) {
                let #ident(#(#pattern_field_names,)*) = self;
                #(
                    ::core_tt_simpler::Contextual::collect_usages(#field_names, usages);
                )*
            }

            fn filter_usages(&mut self, usages: &::core_tt_simpler::Usages) {
                let #ident(#(#pattern_field_names,)*) = self;
                #(
                    ::core_tt_simpler::Contextual::filter_usages(#field_names, usages);
                )*
            }

            fn unfilter_usages(&mut self, usages: &::core_tt_simpler::Usages) {
                let #ident(#(#pattern_field_names,)*) = self;
                #(
                    ::core_tt_simpler::Contextual::unfilter_usages(#field_names, usages);
                )*
            }
        }
    }
}

fn derive_contextual_enum(
    ident: syn::Ident,
    mut generics: syn::Generics,
    data_enum: syn::DataEnum,
) -> proc_macro2::TokenStream {
    let syn::DataEnum { enum_token: _, brace_token: _, variants } = data_enum;

    let ctx_len_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .filter_map(|field| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(field.ident.as_ref().unwrap())
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* .. } => {
                            let ret = 0;
                            #(
                                let ret = ::core::cmp::max(
                                    ret,
                                    ::core_tt_simpler::Contextual::ctx_len(#field_names),
                                );
                            )*
                            ret
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let pattern_field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                Some(format_ident!("_field_{}", index))
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    let field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .filter_map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#pattern_field_names,)*) => {
                            let ret = 0;
                            #(
                                let ret = ::core::cmp::max(
                                    ret,
                                    ::core_tt_simpler::Contextual::ctx_len(#field_names),
                                );
                            )*
                            ret
                        },
                    }
                },
                Fields::Unit => {
                    quote! {
                        #ident::#variant_ident => 0,
                    }
                },
            }
        })
    };

    let collect_usages_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .filter_map(|field| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(field.ident.as_ref().unwrap())
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* .. } => {
                            #(
                                ::core_tt_simpler::Contextual::collect_usages(#field_names, usages);
                            )*
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let pattern_field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                Some(format_ident!("_field_{}", index))
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    let field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .filter_map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#pattern_field_names,)*) => {
                            #(
                                ::core_tt_simpler::Contextual::collect_usages(#field_names, usages);
                            )*
                        },
                    }
                },
                Fields::Unit => {
                    quote! {
                        #ident::#variant_ident => {
                            let _ = usages;
                        },
                    }
                },
            }
        })
    };

    let filter_usages_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .filter_map(|field| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(field.ident.as_ref().unwrap())
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* .. } => {
                            #(
                                ::core_tt_simpler::Contextual::filter_usages(#field_names, usages);
                            )*
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let pattern_field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                Some(format_ident!("_field_{}", index))
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    let field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .filter_map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#pattern_field_names,)*) => {
                            #(
                                ::core_tt_simpler::Contextual::filter_usages(#field_names, usages);
                            )*
                        },
                    }
                },
                Fields::Unit => {
                    quote! {
                        #ident::#variant_ident => {
                            let _ = usages;
                        },
                    }
                },
            }
        })
    };

    let unfilter_usages_branches = {
        variants
        .iter()
        .map(|variant| {
            let syn::Variant { attrs: _, ident: variant_ident, fields, discriminant: _ } = variant;
            match fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = {
                        fields
                        .named
                        .iter()
                        .filter_map(|field| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(field.ident.as_ref().unwrap())
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident { #(#field_names,)* .. } => {
                            #(
                                ::core_tt_simpler::Contextual::unfilter_usages(#field_names, usages);
                            )*
                        },
                    }
                },
                Fields::Unnamed(fields) => {
                    let pattern_field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                Some(format_ident!("_field_{}", index))
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    let field_names: Vec<_> = {
                        fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .filter_map(|(index, field)| {
                            if attributes_contain_ignore(&field.attrs) {
                                None
                            } else {
                                Some(format_ident!("field_{}", index))
                            }
                        })
                        .collect()
                    };
                    quote! {
                        #ident::#variant_ident(#(#pattern_field_names,)*) => {
                            #(
                                ::core_tt_simpler::Contextual::unfilter_usages(#field_names, usages);
                            )*
                        },
                    }
                },
                Fields::Unit => {
                    quote! {
                        #ident::#variant_ident => {
                            let _ = usages;
                        },
                    }
                },
            }
        })
    };

    make_generic_where_clauses(&mut generics);
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        impl #impl_generics ::core_tt_simpler::Contextual for #ident #type_generics
        #where_clause
        {
            fn ctx_len(&self) -> usize {
                match self {
                    #(#ctx_len_branches)*
                }
            }

            fn collect_usages(&self, usages: &mut core_tt_simpler::Usages) {
                match self {
                    #(#collect_usages_branches)*
                }
            }

            fn filter_usages(&mut self, usages: &core_tt_simpler::Usages) {
                match self {
                    #(#filter_usages_branches)*
                }
            }

            fn unfilter_usages(&mut self, usages: &core_tt_simpler::Usages) {
                match self {
                    #(#unfilter_usages_branches)*
                }
            }
        }
    }
}

fn derive_contextual_unit_struct(
    ident: syn::Ident,
    mut generics: syn::Generics,
) -> proc_macro2::TokenStream {
    make_generic_where_clauses(&mut generics);
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    quote! {
        impl #impl_generics ::core_tt_simpler::Contextual for #ident #type_generics
        #where_clause
        {
            fn ctx_len(&self) -> usize {
                0
            }
            
            fn collect_usages(&self, usages: &mut ::core_tt_simpler::Usages) {
                let _ = usages;
            }
            
            fn filter_usages(&mut self, usages: &::core_tt_simpler::Usages) {
                let _ = usages;
            }
            
            fn unfilter_usages(&mut self, usages: &::core_tt_simpler::Usages) {
                let _ = usages;
            }
        }
    }
}

