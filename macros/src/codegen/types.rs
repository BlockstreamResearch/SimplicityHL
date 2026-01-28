use quote::quote;
use simplicityhl::ResolvedType;

/// Recursive Rust type representation for code generation
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum RustType {
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
    pub fn from_resolved_type(ty: &ResolvedType) -> syn::Result<Self> {
        use simplicityhl::types::{TypeInner, UIntType};

        match ty.as_inner() {
            TypeInner::Boolean => Ok(RustType::Bool),
            TypeInner::UInt(uint_ty) => match uint_ty {
                UIntType::U1 => Ok(RustType::Bool),
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
    pub fn to_type_token_stream(&self) -> proc_macro2::TokenStream {
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
    pub fn generate_to_simplicity_conversion(
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

    pub fn generate_simplicity_type_construction(&self) -> proc_macro2::TokenStream {
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

    pub fn generate_from_value_extraction(
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

    pub fn generate_inline_array_element_extraction(
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

    pub fn generate_inline_tuple_element_extraction(
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

    pub fn generate_inline_either_extraction(
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
