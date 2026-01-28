use crate::codegen::types::RustType;
use crate::convert_error_to_syn;
use crate::parse::SimfContent;
use quote::{format_ident, quote};
use simplicityhl::str::WitnessName;
use simplicityhl::{AbiMeta, Parameters, ResolvedType, TemplateProgram, WitnessTypes};
use std::error::Error;

// TODO(Illia): add bincode generation feature (i.e. require bincode dependencies)
// TODO(Illia): add conditional compilation for simplicity-core to e included automatically

// TODO(Illia): automatically derive bincode implementation
// TODO(Illia): extract either:serde feature and use it when simplicityhl has serde feature
// TODO(Illia): add features

mod types;

pub fn compile_program(content: &SimfContent) -> syn::Result<AbiMeta> {
    compile_program_inner(content).map_err(|e| convert_error_to_syn(e))
}

fn compile_program_inner(content: &SimfContent) -> Result<AbiMeta, Box<dyn Error>> {
    let program = content.content.as_str();
    Ok(TemplateProgram::new(program)?.generate_abi_meta()?)
}

pub fn gen_helpers(
    simf_content: SimfContent,
    meta: AbiMeta,
) -> syn::Result<proc_macro2::TokenStream> {
    gen_helpers_inner(simf_content, meta).map_err(|e| convert_error_to_syn(e))
}

struct DerivedMeta {
    contract_source_const_name: proc_macro2::Ident,
    args_struct: ConvertedMeta,
    witness_struct: ConvertedMeta,
    simf_content: SimfContent,
    abi_meta: AbiMeta,
}

impl DerivedMeta {
    fn try_from(simf_content: SimfContent, abi_meta: AbiMeta) -> syn::Result<Self> {
        let args_struct = ConvertedMeta::generate_args_struct(
            &simf_content.contract_name,
            &abi_meta.param_types,
        )?;
        let witness_struct = ConvertedMeta::generate_witness_struct(
            &simf_content.contract_name,
            &abi_meta.witness_types,
        )?;
        let contract_source_const_name = format_ident!(
            "{}_CONTRACT_SOURCE",
            simf_content.contract_name.to_uppercase()
        );
        Ok(DerivedMeta {
            contract_source_const_name,
            args_struct,
            witness_struct,
            simf_content,
            abi_meta,
        })
    }
}

fn gen_helpers_inner(
    simf_content: SimfContent,
    meta: AbiMeta,
) -> Result<proc_macro2::TokenStream, Box<dyn Error>> {
    let mod_ident = format_ident!("derived_{}", simf_content.contract_name);

    let derived_meta = DerivedMeta::try_from(simf_content, meta)?;

    let program_helpers = construct_program_helpers(&derived_meta);
    let witness_helpers = construct_witness_helpers(&derived_meta)?;
    let arguments_helpers = construct_argument_helpers(&derived_meta)?;

    Ok(quote! {
        pub mod #mod_ident{
            #program_helpers

            #witness_helpers

            #arguments_helpers
        }
    })
}

fn construct_program_helpers(derived_meta: &DerivedMeta) -> proc_macro2::TokenStream {
    let contract_content = &derived_meta.simf_content.content;
    let error_msg = format!(
        "INTERNAL: expected '{}' Program to compile successfully.",
        derived_meta.simf_content.contract_name
    );
    let contract_source_name = &derived_meta.contract_source_const_name;
    let contract_arguments_struct_name = &derived_meta.args_struct.struct_name;

    quote! {
        use simplicityhl::elements::Address;
        use simplicityhl::simplicity::bitcoin::XOnlyPublicKey;
        use simplicityhl_core::{create_p2tr_address, load_program, ProgramError, SimplicityNetwork};
        use simplicityhl::CompiledProgram;

        pub const #contract_source_name: &str = #contract_content;

        /// Get the options template program for instantiation.
        ///
        /// # Panics
        /// - if the embedded source fails to compile (should never happen).
        #[must_use]
        pub fn get_template_program() -> ::simplicityhl::TemplateProgram {
            ::simplicityhl::TemplateProgram::new(#contract_source_name).expect(#error_msg)
        }

        /// Derive P2TR address for an option offer contract.
        ///
        /// # Errors
        ///
        /// Returns error if program compilation fails.
        pub fn get_option_offer_address(
            x_only_public_key: &XOnlyPublicKey,
            arguments: &#contract_arguments_struct_name,
            network: SimplicityNetwork,
        ) -> Result<Address, ProgramError> {
            Ok(create_p2tr_address(
                get_loaded_program(arguments)?.commit().cmr(),
                x_only_public_key,
                network.address_params(),
            ))
        }

        /// Compile option offer program with the given arguments.
        ///
        /// # Errors
        ///
        /// Returns error if compilation fails.
        pub fn get_loaded_program(
            arguments: &#contract_arguments_struct_name,
        ) -> Result<CompiledProgram, ProgramError> {
            load_program(#contract_source_name, arguments.build_arguments())
        }

        /// Get compiled option offer program, panicking on failure.
        ///
        /// # Panics
        ///
        /// Panics if program instantiation fails.
        #[must_use]
        pub fn get_compiled_program(arguments: &#contract_arguments_struct_name) -> CompiledProgram {
            let program = get_template_program();

            program
                .instantiate(arguments.build_arguments(), true)
                .unwrap()
        }
    }
}

struct WitnessField {
    witness_simf_name: String,
    struct_rust_field: proc_macro2::Ident,
    rust_type: RustType,
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

fn construct_witness_helpers(derived_meta: &DerivedMeta) -> syn::Result<proc_macro2::TokenStream> {
    let GeneratedWitnessTokens {
        imports,
        struct_token_stream,
        struct_impl,
    } = derived_meta.witness_struct.generate_witness_impl()?;

    Ok(quote! {
        pub use build_witness::*;
        mod build_witness {
            #imports

            #struct_token_stream

            #struct_impl
        }
    })
}

fn construct_argument_helpers(derived_meta: &DerivedMeta) -> syn::Result<proc_macro2::TokenStream> {
    let GeneratedArgumentsTokens {
        imports,
        struct_token_stream,
        struct_impl,
    } = derived_meta.args_struct.generate_arguments_impl()?;

    Ok(quote! {
        pub use build_arguments::*;
        mod build_arguments {
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
            witness_values: ConvertedMeta::generate_witness_fields(meta.iter())?,
        })
    }

    fn generate_witness_struct(
        contract_name: &str,
        meta: &WitnessTypes,
    ) -> syn::Result<ConvertedMeta> {
        let base_name = convert_contract_name_to_struct_name(contract_name);
        Ok(ConvertedMeta {
            struct_name: format_ident!("{}Witness", base_name),
            witness_values: ConvertedMeta::generate_witness_fields(meta.iter())?,
        })
    }

    fn generate_witness_fields<'a>(
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
                    use bincode::*;
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
            // #[derive(bincode::Encode, bincode::Decode)]
            #[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
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
    let words: Vec<String> = contract_name
        .split('_')
        .filter(|w| !w.is_empty())
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
            }
        })
        .collect();
    words.join("")
}
