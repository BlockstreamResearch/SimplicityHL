use crate::convert_error_to_syn;
use crate::parse::SimfContent;
use quote::{format_ident, quote};
use simplicityhl::str::WitnessName;
use simplicityhl::{AbiMeta, Parameters, ResolvedType, TemplateProgram, WitnessTypes};
use std::error::Error;

pub fn compile_program(content: &SimfContent) -> syn::Result<AbiMeta> {
    compile_program_inner(content).map_err(|e| convert_error_to_syn(e))
}

fn compile_program_inner(content: &SimfContent) -> Result<AbiMeta, Box<dyn Error>> {
    let program = content.content.as_str();
    Ok(TemplateProgram::new(program)?.generate_abi_meta()?)
}

pub fn gen_helpers(
    simf_content: &SimfContent,
    meta: &AbiMeta,
) -> syn::Result<proc_macro2::TokenStream> {
    gen_helpers_inner(&simf_content, meta).map_err(|e| convert_error_to_syn(e))
}

fn gen_helpers_inner(
    simf_content: &SimfContent,
    meta: &AbiMeta,
) -> Result<proc_macro2::TokenStream, Box<dyn Error>> {
    let mod_ident = format_ident!("{}", simf_content.contract_name);
    let program_helpers = construct_program_helpers(simf_content, meta);
    let witness_helpers = construct_witness_helpers(simf_content, meta)?;
    let arguments_helpers = construct_argument_helpers(simf_content, meta)?;

    Ok(quote! {
        pub mod #mod_ident{
            #program_helpers

            #witness_helpers

            #arguments_helpers
        }
    })
}

fn construct_program_helpers(
    simf_content: &SimfContent,
    _meta: &AbiMeta,
) -> proc_macro2::TokenStream {
    let contract_content = &simf_content.content;
    let error_msg = format!(
        "INTERNAL: expected '{}' Program to compile successfully.",
        simf_content.contract_name
    );

    quote! {
        pub const CONTRACT_SOURCE: &str = #contract_content;

        /// Get the options template program for instantiation.
        ///
        /// # Panics
        /// - if the embedded source fails to compile (should never happen).
        #[must_use]
        pub fn get_options_template_program() -> ::simplicityhl::TemplateProgram {
            ::simplicityhl::TemplateProgram::new(CONTRACT_SOURCE).expect(#error_msg)
        }
    }
}

struct WitnessField {
    witness_simf_name: String,
    struct_rust_field: proc_macro2::Ident,
    rust_type: RustType,
}

/// Recursive Rust type representation for code generation
#[derive(Debug, Clone)]
#[non_exhaustive]
enum RustType {
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256Array,
    Array(Box<RustType>, usize),
    Tuple(Vec<RustType>),
    Either(Box<RustType>, Box<RustType>),
    Option(Box<RustType>),
}

impl RustType {
    /// Convert a Simplicity ResolvedType to a Rust type representation
    fn from_resolved_type(ty: &ResolvedType) -> syn::Result<Self> {
        use simplicityhl::types::{TypeInner, UIntType};

        match ty.as_inner() {
            TypeInner::Boolean => Ok(RustType::Bool),
            TypeInner::UInt(uint_ty) => match uint_ty {
                UIntType::U1 => Ok(RustType::Bool), // u1 maps to bool
                UIntType::U2 | UIntType::U4 | UIntType::U8 => Ok(RustType::U8),
                UIntType::U16 => Ok(RustType::U16),
                UIntType::U32 => Ok(RustType::U32),
                UIntType::U64 => Ok(RustType::U64),
                UIntType::U128 => Ok(RustType::U128),
                UIntType::U256 => Ok(RustType::U256Array),
            },
            TypeInner::Either(left, right) => {
                let left_ty = Self::from_resolved_type(left)?;
                let right_ty = Self::from_resolved_type(right)?;
                Ok(RustType::Either(Box::new(left_ty), Box::new(right_ty)))
            }
            TypeInner::Option(inner) => {
                let inner_ty = Self::from_resolved_type(inner)?;
                Ok(RustType::Option(Box::new(inner_ty)))
            }
            TypeInner::Tuple(elements) => {
                let element_types: syn::Result<Vec<_>> = elements
                    .iter()
                    .map(|e| Self::from_resolved_type(e))
                    .collect();
                Ok(RustType::Tuple(element_types?))
            }
            TypeInner::Array(element, size) => {
                let element_ty = Self::from_resolved_type(element)?;
                Ok(RustType::Array(Box::new(element_ty), *size))
            }
            TypeInner::List(_, _) => Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "List types are not yet supported in macro conversions",
            )),
            _ => Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "Unsupported type in macro conversions",
            )),
        }
    }

    /// Generate the Rust type as a TokenStream for struct field declarations
    fn to_type_token_stream(&self) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => quote! { bool },
            RustType::U8 => quote! { u8 },
            RustType::U16 => quote! { u16 },
            RustType::U32 => quote! { u32 },
            RustType::U64 => quote! { u64 },
            RustType::U128 => quote! { u128 },
            RustType::U256Array => quote! { [u8; 32] },
            RustType::Array(element, size) => {
                let element_ty = element.to_type_token_stream();
                quote! { [#element_ty; #size] }
            }
            RustType::Tuple(elements) => {
                let element_types: Vec<_> =
                    elements.iter().map(|e| e.to_type_token_stream()).collect();
                quote! { (#(#element_types),*) }
            }
            RustType::Either(left, right) => {
                let left_ty = left.to_type_token_stream();
                let right_ty = right.to_type_token_stream();
                quote! { ::simplicityhl::either::Either<#left_ty, #right_ty> }
            }
            RustType::Option(inner) => {
                let inner_ty = inner.to_type_token_stream();
                quote! { Option<#inner_ty> }
            }
        }
    }

    /// Generate conversion code from Rust value to Simplicity Value
    /// `value_expr` is the expression that produces the Rust value to convert
    fn generate_to_simplicity_conversion(
        &self,
        value_expr: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => {
                quote! { Value::from(#value_expr) }
            }
            RustType::U8 => {
                quote! { Value::from(UIntValue::U8(#value_expr)) }
            }
            RustType::U16 => {
                quote! { Value::from(UIntValue::U16(#value_expr)) }
            }
            RustType::U32 => {
                quote! { Value::from(UIntValue::U32(#value_expr)) }
            }
            RustType::U64 => {
                quote! { Value::from(UIntValue::U64(#value_expr)) }
            }
            RustType::U128 => {
                quote! { Value::from(UIntValue::U128(#value_expr)) }
            }
            RustType::U256Array => {
                quote! { Value::from(UIntValue::U256(U256::from_byte_array(#value_expr))) }
            }
            RustType::Array(element, size) => {
                // For arrays, we need to generate inline conversions
                let indices: Vec<_> = (0..*size).map(syn::Index::from).collect();
                let element_conversions: Vec<_> = indices
                    .iter()
                    .map(|idx| {
                        let elem_expr = quote! { #value_expr[#idx] };
                        element.generate_to_simplicity_conversion(elem_expr)
                    })
                    .collect();

                // Generate the element type token stream for type inference
                let elem_ty_generation = element.generate_simplicity_type_construction();

                quote! {
                    {
                        let elements = [#(#element_conversions),*];
                        Value::array(elements, #elem_ty_generation)
                    }
                }
            }
            RustType::Tuple(elements) => {
                if elements.is_empty() {
                    quote! { Value::unit() }
                } else {
                    let tuple_conversions = elements.iter().enumerate().map(|(i, elem_ty)| {
                        let idx = syn::Index::from(i);
                        let elem_expr = quote! { #value_expr.#idx };
                        elem_ty.generate_to_simplicity_conversion(elem_expr)
                    });

                    quote! {
                        Value::tuple([#(#tuple_conversions),*])
                    }
                }
            }
            RustType::Either(left, right) => {
                let left_conv = left.generate_to_simplicity_conversion(quote! { left_val });
                let right_conv = right.generate_to_simplicity_conversion(quote! { right_val });
                let left_ty = left.generate_simplicity_type_construction();
                let right_ty = right.generate_simplicity_type_construction();

                quote! {
                    match &#value_expr {
                        ::simplicityhl::either::Either::Left(left_val) => {
                            Value::left(
                                #left_conv,
                                #right_ty
                            )
                        }
                        ::simplicityhl::either::Either::Right(right_val) => {
                            Value::right(
                                #left_ty,
                                #right_conv
                            )
                        }
                    }
                }
            }
            RustType::Option(inner) => {
                let inner_conv = inner.generate_to_simplicity_conversion(quote! { inner_val });
                let inner_ty = inner.generate_simplicity_type_construction();

                quote! {
                    match &#value_expr {
                        None => {
                            Value::none(#inner_ty)
                        }
                        Some(inner_val) => {
                            Value::some(#inner_conv)
                        }
                    }
                }
            }
        }
    }

    fn generate_simplicity_type_construction(&self) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => {
                quote! { ResolvedType::boolean() }
            }
            RustType::U8 => {
                quote! { ResolvedType::u8() }
            }
            RustType::U16 => {
                quote! { ResolvedType::u16() }
            }
            RustType::U32 => {
                quote! { ResolvedType::u32() }
            }
            RustType::U64 => {
                quote! { ResolvedType::u64() }
            }
            RustType::U128 => {
                quote! { ResolvedType::u128() }
            }
            RustType::U256Array => {
                quote! { ResolvedType::u256() }
            }
            RustType::Array(element, size) => {
                let elem_ty = element.generate_simplicity_type_construction();
                quote! { ResolvedType::array(#elem_ty, #size) }
            }
            RustType::Tuple(elements) => {
                let elem_types: Vec<_> = elements
                    .iter()
                    .map(|e| e.generate_simplicity_type_construction())
                    .collect();
                quote! { ResolvedType::tuple([#(#elem_types),*]) }
            }
            RustType::Either(left, right) => {
                let left_ty = left.generate_simplicity_type_construction();
                let right_ty = right.generate_simplicity_type_construction();
                quote! { ResolvedType::either(#left_ty, #right_ty) }
            }
            RustType::Option(inner) => {
                let inner_ty = inner.generate_simplicity_type_construction();
                quote! { ResolvedType::option(#inner_ty) }
            }
        }
    }

    /// Generate code to extract a Rust value from Arguments/WitnessValues
    /// `args_expr` is the expression that produces the Arguments/WitnessValues reference
    /// `witness_name` is the name of the witness value to extract
    fn generate_from_value_extraction(
        &self,
        args_expr: proc_macro2::Ident,
        witness_name: &str,
    ) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::Boolean(b) => Ok(*b),
                            _ => Err(format!("Wrong type for {}: expected bool", #witness_name)),
                        }
                    }
                }
            }
            RustType::U8 => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::UInt(UIntValue::U8(v)) => Ok(*v),
                            _ => Err(format!("Wrong type for {}: expected U8", #witness_name)),
                        }
                    }
                }
            }
            RustType::U16 => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::UInt(UIntValue::U16(v)) => Ok(*v),
                            _ => Err(format!("Wrong type for {}: expected U16", #witness_name)),
                        }
                    }
                }
            }
            RustType::U32 => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::UInt(UIntValue::U32(v)) => Ok(*v),
                            _ => Err(format!("Wrong type for {}: expected U32", #witness_name)),
                        }
                    }
                }
            }
            RustType::U64 => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::UInt(UIntValue::U64(v)) => Ok(*v),
                            _ => Err(format!("Wrong type for {}: expected U64", #witness_name)),
                        }
                    }
                }
            }
            RustType::U128 => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::UInt(UIntValue::U128(v)) => Ok(*v),
                            _ => Err(format!("Wrong type for {}: expected U128", #witness_name)),
                        }
                    }
                }
            }
            RustType::U256Array => {
                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::UInt(UIntValue::U256(u256)) => Ok(u256.to_byte_array()),
                            _ => Err(format!("Wrong type for {}: expected U256", #witness_name)),
                        }
                    }
                }
            }
            RustType::Array(element, size) => {
                let elem_extraction = (0..*size).map(|i| {
                    // For each element, generate extraction code
                    // This is a simplified version - for complex nested types,
                    // we'd need to extract from array values
                    element.generate_inline_array_element_extraction(quote! { arr_value }, i)
                });

                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::Array(arr_value) => {
                                if arr_value.len() != #size {
                                    return Err(format!("Wrong array length for {}: expected {}, got {}", #witness_name, #size, arr_value.len()));
                                }
                                Ok([#(#elem_extraction),*])
                            }
                            _ => Err(format!("Wrong type for {}: expected Array", #witness_name)),
                        }
                    }
                }
            }
            RustType::Tuple(elements) => {
                let elem_extractions: Vec<_> = elements
                    .iter()
                    .enumerate()
                    .map(|(i, elem_ty)| {
                        elem_ty.generate_inline_tuple_element_extraction(quote! { tuple_value }, i)
                    })
                    .collect();

                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::Tuple(tuple_value) => {
                                if tuple_value.len() != #(elements.len()) {
                                    return Err(format!("Wrong tuple length for {}", #witness_name));
                                }
                                Ok((#(#elem_extractions),*))
                            }
                            _ => Err(format!("Wrong type for {}: expected Tuple", #witness_name)),
                        }
                    }
                }
            }
            //TODO: redo
            RustType::Either(left, right) => {
                let left_extraction = left.generate_inline_either_extraction(quote! { left_val });
                let right_extraction =
                    right.generate_inline_either_extraction(quote! { right_val });

                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::Either(either_val) => {
                                match either_val {
                                    ::simplicityhl::either::Either::Left(left_val) => {
                                        Ok(::simplicityhl::either::Either::Left(#left_extraction?))
                                    }
                                    ::simplicityhl::either::Either::Right(right_val) => {
                                        Ok(::simplicityhl::either::Either::Right(#right_extraction?))
                                    }
                                }
                            }
                            _ => Err(format!("Wrong type for {}: expected Either", #witness_name)),
                        }
                    }
                }
            }
            // TODO: redo
            RustType::Option(inner) => {
                let inner_extraction = inner.generate_inline_either_extraction(quote! { some_val });

                quote! {
                    {
                        let witness_name = WitnessName::from_str_unchecked(#witness_name);
                        let value = #args_expr
                            .get(&witness_name)
                            .ok_or_else(|| format!("Missing witness: {}", #witness_name))?;
                        match value.inner() {
                            simplicityhl::value::ValueInner::Option(opt_val) => {
                                match opt_val {
                                    None => Ok(None),
                                    Some(some_val) => Ok(Some(#inner_extraction?)),
                                }
                            }
                            _ => Err(format!("Wrong type for {}: expected Option", #witness_name)),
                        }
                    }
                }
            }
        }
    }

    /// Generate inline extraction code for array elements
    fn generate_inline_array_element_extraction(
        &self,
        arr_expr: proc_macro2::TokenStream,
        index: usize,
    ) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::Boolean(b) => *b,
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            RustType::U8 => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U8(v)) => *v,
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            RustType::U16 => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U16(v)) => *v,
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            RustType::U32 => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U32(v)) => *v,
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            RustType::U64 => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U64(v)) => *v,
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            RustType::U128 => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U128(v)) => *v,
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            RustType::U256Array => quote! {
                match #arr_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U256(u256)) => u256.to_byte_array(),
                    _ => return Err(format!("Wrong element type at index {}", #index)),
                }
            },
            _ => quote! {
                return Err(format!("Complex array element extraction not yet supported at index {}", #index))
            },
        }
    }

    /// Generate inline extraction code for tuple elements
    fn generate_inline_tuple_element_extraction(
        &self,
        tuple_expr: proc_macro2::TokenStream,
        index: usize,
    ) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::Boolean(b) => *b,
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::U8 => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U8(v)) => *v,
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::U16 => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U16(v)) => *v,
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::U32 => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U32(v)) => *v,
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::U64 => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U64(v)) => *v,
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::U128 => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U128(v)) => *v,
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::U256Array => quote! {
                match #tuple_expr[#index].inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U256(u256)) => u256.to_byte_array(),
                    _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                }
            },
            RustType::Tuple(elements) => {
                let elem_extractions: Vec<_> = elements
                    .iter()
                    .enumerate()
                    .map(|(i, elem_ty)| {
                        elem_ty.generate_inline_tuple_element_extraction(quote! { nested_tuple }, i)
                    })
                    .collect();

                quote! {
                    match #tuple_expr[#index].inner() {
                        simplicityhl::value::ValueInner::Tuple(nested_tuple) => {
                            (#(#elem_extractions),*)
                        }
                        _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                    }
                }
            }
            RustType::Either(left, right) => {
                let left_extraction = left.generate_inline_either_extraction(quote! { left_val });
                let right_extraction =
                    right.generate_inline_either_extraction(quote! { right_val });

                quote! {
                    match #tuple_expr[#index].inner() {
                        simplicityhl::value::ValueInner::Either(either_val) => {
                            match either_val {
                                ::simplicityhl::either::Either::Left(left_val) => {
                                    ::simplicityhl::either::Either::Left(match { #left_extraction } {
                                        Ok(v) => v,
                                        Err(e) => return Err(e),
                                    })
                                }
                                ::simplicityhl::either::Either::Right(right_val) => {
                                    ::simplicityhl::either::Either::Right(match { #right_extraction } {
                                        Ok(v) => v,
                                        Err(e) => return Err(e),
                                    })
                                }
                            }
                        }
                        _ => return Err(format!("Wrong tuple element type at index {}", #index)),
                    }
                }
            }
            _ => quote! {
                return Err(format!("Complex tuple element extraction not yet supported at index {}", #index))
            },
        }
    }

    /// Generate inline extraction code for either branches
    fn generate_inline_either_extraction(
        &self,
        val_expr: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match self {
            RustType::Bool => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::Boolean(b) => Ok(*b),
                    _ => Err("Wrong either branch type: expected bool".to_string()),
                }
            },
            RustType::U8 => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U8(v)) => Ok(*v),
                    _ => Err("Wrong either branch type: expected U8".to_string()),
                }
            },
            RustType::U16 => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U16(v)) => Ok(*v),
                    _ => Err("Wrong either branch type: expected U16".to_string()),
                }
            },
            RustType::U32 => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U32(v)) => Ok(*v),
                    _ => Err("Wrong either branch type: expected U32".to_string()),
                }
            },
            RustType::U64 => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U64(v)) => Ok(*v),
                    _ => Err("Wrong either branch type: expected U64".to_string()),
                }
            },
            RustType::U128 => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U128(v)) => Ok(*v),
                    _ => Err("Wrong either branch type: expected U128".to_string()),
                }
            },
            RustType::U256Array => quote! {
                match #val_expr.inner() {
                    simplicityhl::value::ValueInner::UInt(UIntValue::U256(u256)) => Ok(u256.to_byte_array()),
                    _ => Err("Wrong either branch type: expected U256".to_string()),
                }
            },
            RustType::Tuple(elements) => {
                let elem_extractions: Vec<_> = elements
                    .iter()
                    .enumerate()
                    .map(|(i, elem_ty)| {
                        elem_ty.generate_inline_tuple_element_extraction(quote! { tuple_value }, i)
                    })
                    .collect();

                quote! {
                    match #val_expr.inner() {
                        simplicityhl::value::ValueInner::Tuple(tuple_value) => {
                            Ok((#(#elem_extractions),*))
                        }
                        _ => Err("Wrong either branch type: expected Tuple".to_string()),
                    }
                }
            }
            RustType::Either(left, right) => {
                let left_extraction = left.generate_inline_either_extraction(quote! { left_val });
                let right_extraction =
                    right.generate_inline_either_extraction(quote! { right_val });

                quote! {
                    match #val_expr.inner() {
                        simplicityhl::value::ValueInner::Either(either_val) => {
                            match either_val {
                                ::simplicityhl::either::Either::Left(left_val) => {
                                    Ok(::simplicityhl::either::Either::Left(#left_extraction?))
                                }
                                ::simplicityhl::either::Either::Right(right_val) => {
                                    Ok(::simplicityhl::either::Either::Right(#right_extraction?))
                                }
                            }
                        }
                        _ => Err("Wrong either branch type: expected Either".to_string()),
                    }
                }
            }
            _ => quote! {
                Err("Complex either branch extraction not yet supported".to_string())
            },
        }
    }
}

impl WitnessField {
    fn new(witness_name: &WitnessName, resolved_type: &ResolvedType) -> syn::Result<Self> {
        let (witness_simf_name, struct_rust_field) = {
            let w_name = witness_name.to_string();
            let r_name = format_ident!("{}", w_name.to_lowercase());
            (w_name, r_name)
        };

        let rust_type = RustType::from_resolved_type(resolved_type)?;

        Ok(Self {
            witness_simf_name,
            struct_rust_field,
            rust_type,
        })
    }

    /// Generate the conversion code from Rust value to Simplicity Value
    fn to_token_stream(&self) -> proc_macro2::TokenStream {
        let witness_name = &self.witness_simf_name;
        let field_name = &self.struct_rust_field;
        let conversion = self
            .rust_type
            .generate_to_simplicity_conversion(quote! { self.#field_name });

        quote! {
            (
                ::simplicityhl::str::WitnessName::from_str_unchecked(#witness_name),
                #conversion
            )
        }
    }
}

fn construct_witness_helpers(
    simf_content: &SimfContent,
    meta: &AbiMeta,
) -> syn::Result<proc_macro2::TokenStream> {
    let args_struct =
        ConvertedMeta::generate_witness_struct(&simf_content.contract_name, &meta.witness_types)?;

    let GeneratedWitnessTokens {
        imports,
        struct_token_stream,
        struct_impl,
    } = args_struct.generate_witness_impl()?;

    Ok(quote! {
        pub mod build_witness {
            #imports

            #struct_token_stream

            #struct_impl
        }
    })
}

fn construct_argument_helpers(
    simf_content: &SimfContent,
    meta: &AbiMeta,
) -> syn::Result<proc_macro2::TokenStream> {
    let args_struct =
        ConvertedMeta::generate_args_struct(&simf_content.contract_name, &meta.param_types)?;

    let GeneratedArgumentsTokens {
        imports,
        struct_token_stream,
        struct_impl,
    } = args_struct.generate_arguments_impl()?;

    Ok(quote! {
        pub mod build_arguments {
            #imports

            #struct_token_stream

            #struct_impl
        }
    })
}

struct ConvertedMeta {
    struct_name: proc_macro2::Ident,
    witness_values: Vec<WitnessField>,
}

struct GeneratedArgumentsTokens {
    imports: proc_macro2::TokenStream,
    struct_token_stream: proc_macro2::TokenStream,
    struct_impl: proc_macro2::TokenStream,
}

struct GeneratedWitnessTokens {
    imports: proc_macro2::TokenStream,
    struct_token_stream: proc_macro2::TokenStream,
    struct_impl: proc_macro2::TokenStream,
}

impl ConvertedMeta {
    fn generate_args_struct(contract_name: &str, meta: &Parameters) -> syn::Result<ConvertedMeta> {
        let base_name = convert_contract_name_to_struct_name(contract_name);
        Ok(ConvertedMeta {
            struct_name: format_ident!("{}Arguments", base_name),
            witness_values: ConvertedMeta::generate_witness(meta.iter())?,
        })
    }

    fn generate_witness_struct(
        contract_name: &str,
        meta: &WitnessTypes,
    ) -> syn::Result<ConvertedMeta> {
        let base_name = convert_contract_name_to_struct_name(contract_name);
        Ok(ConvertedMeta {
            struct_name: format_ident!("{}Witness", base_name),
            witness_values: ConvertedMeta::generate_witness(meta.iter())?,
        })
    }

    fn generate_witness<'a>(
        iter: impl Iterator<Item = (&'a WitnessName, &'a ResolvedType)>,
    ) -> syn::Result<Vec<WitnessField>> {
        iter.map(|(name, resolved_type)| WitnessField::new(name, resolved_type))
            .collect()
    }

    fn generate_arguments_impl(&self) -> syn::Result<GeneratedArgumentsTokens> {
        let generated_struct = self.generate_struct_token_stream();
        let struct_name = &self.struct_name;
        let tuples: Vec<proc_macro2::TokenStream> = self.construct_witness_tuples();
        let (arguments_conversion_from_args_map, struct_to_return): (
            proc_macro2::TokenStream,
            proc_macro2::TokenStream,
        ) = self.generate_from_args_conversion_with_param_name("args");

        Ok(GeneratedArgumentsTokens {
            imports: quote! {
                    use std::collections::HashMap;
                    use simplicityhl::{Arguments, Value, ResolvedType};
                    use simplicityhl::value::{UIntValue, ValueInner};
                    use simplicityhl::num::U256;
                    use simplicityhl::str::WitnessName;
                    use simplicityhl::types::TypeConstructible;
                    use simplicityhl::value::ValueConstructible;
            },
            struct_token_stream: quote! {
                #generated_struct
            },
            struct_impl: quote! {
                impl #struct_name {
                    /// Build Simplicity arguments for contract instantiation.
                    #[must_use]
                    pub fn build_arguments(&self) -> simplicityhl::Arguments {
                        simplicityhl::Arguments::from(HashMap::from([
                            #(#tuples),*
                        ]))
                    }

                    /// Build struct from Simplicity Arguments.
                    ///
                    /// # Errors
                    ///
                    /// Returns error if any required witness is missing, has wrong type, or has invalid value.
                    pub fn from_arguments(args: &Arguments) -> Result<Self, String> {
                        #arguments_conversion_from_args_map

                        Ok(#struct_to_return)
                    }
                }
            },
        })
    }

    fn generate_witness_impl(&self) -> syn::Result<GeneratedWitnessTokens> {
        let generated_struct = self.generate_struct_token_stream();
        let struct_name = &self.struct_name;
        let tuples: Vec<proc_macro2::TokenStream> = self.construct_witness_tuples();
        let (arguments_conversion_from_args_map, struct_to_return): (
            proc_macro2::TokenStream,
            proc_macro2::TokenStream,
        ) = self.generate_from_args_conversion_with_param_name("witness");

        Ok(GeneratedWitnessTokens {
            imports: quote! {
                    use std::collections::HashMap;
                    use simplicityhl::{WitnessValues, Value, ResolvedType};
                    use simplicityhl::value::{UIntValue, ValueInner};
                    use simplicityhl::num::U256;
                    use simplicityhl::str::WitnessName;
                    use simplicityhl::types::TypeConstructible;
                    use simplicityhl::value::ValueConstructible;
            },
            struct_token_stream: quote! {
                #generated_struct
            },
            struct_impl: quote! {
                impl #struct_name {
                    /// Build Simplicity witness values for contract execution.
                    #[must_use]
                    pub fn build_witness(&self) -> simplicityhl::WitnessValues {
                        simplicityhl::WitnessValues::from(HashMap::from([
                            #(#tuples),*
                        ]))
                    }

                    /// Build struct from Simplicity WitnessValues.
                    ///
                    /// # Errors
                    ///
                    /// Returns error if any required witness is missing, has wrong type, or has invalid value.
                    pub fn from_witness(witness: &WitnessValues) -> Result<Self, String> {
                        #arguments_conversion_from_args_map

                        Ok(#struct_to_return)
                    }
                }
            },
        })
    }

    fn generate_struct_token_stream(&self) -> proc_macro2::TokenStream {
        let name = format_ident!("{}", self.struct_name);
        let fields: Vec<proc_macro2::TokenStream> = self
            .witness_values
            .iter()
            .map(|field| {
                let field_name = format_ident!("{}", field.struct_rust_field);
                let field_type = field.rust_type.to_type_token_stream();
                quote! { pub #field_name: #field_type }
            })
            .collect();
        quote! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub struct #name {
                #(#fields),*
            }
        }
    }

    #[inline]
    fn construct_witness_tuples(&self) -> Vec<proc_macro2::TokenStream> {
        self.witness_values
            .iter()
            .map(|x| x.to_token_stream())
            .collect()
    }

    /// Generate conversion code from Arguments/WitnessValues back to struct fields.
    /// Returns a tuple of (extraction_code, struct_initialization_code).
    fn generate_from_args_conversion_with_param_name(
        &self,
        param_name: &str,
    ) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
        let param_ident = format_ident!("{}", param_name);
        let field_extractions: Vec<proc_macro2::TokenStream> = self
            .witness_values
            .iter()
            .map(|field| {
                let field_name = &field.struct_rust_field;
                let witness_name = &field.witness_simf_name;
                let extraction = field
                    .rust_type
                    .generate_from_value_extraction(param_ident.clone(), witness_name);
                quote! {
                    let #field_name = #extraction?;
                }
            })
            .collect();

        let field_names: Vec<proc_macro2::Ident> = self
            .witness_values
            .iter()
            .map(|field| format_ident!("{}", field.struct_rust_field))
            .collect();

        let extractions = quote! {
            #(#field_extractions)*
        };

        let struct_init = quote! {
            Self {
                #(#field_names),*
            }
        };

        (extractions, struct_init)
    }
}

fn convert_contract_name_to_struct_name(contract_name: &str) -> String {
    let mut chars = contract_name.chars();
    // We assume that the contract name is nonzero
    let first_letter = chars.next().unwrap();
    first_letter.to_uppercase().collect::<String>() + chars.as_str()
}
