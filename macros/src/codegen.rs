use crate::convert_error_to_syn;
use crate::parse::SimfContent;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use simplicityhl::{AbiMeta, TemplateProgram};
use std::error::Error;

pub fn compile_program(content: &SimfContent) -> syn::Result<AbiMeta> {
    compile_program_inner(content).map_err(|e| convert_error_to_syn(e))
}

pub fn gen_helpers(simf_content: &SimfContent, meta: AbiMeta) -> syn::Result<TokenStream> {
    gen_helpers_inner(&simf_content.contract_name, meta).map_err(|e| convert_error_to_syn(e))
}

fn gen_helpers_inner(contract_name: &str, meta: AbiMeta) -> Result<TokenStream, Box<dyn Error>> {
    let str = format!("{meta:?}");
    let mod_ident = format_ident!("{contract_name}_hello1");
    let name2 = format_ident!("{contract_name}_hello2");
    Ok(quote! {
        pub mod #mod_ident{
            pub const #mod_ident: &'static str = #contract_name;
            pub const #name2: &'static str = #str;
            }
    }
    .into_token_stream())
}

fn compile_program_inner(content: &SimfContent) -> Result<AbiMeta, Box<dyn Error>> {
    let program = content.content.as_str();
    Ok(TemplateProgram::new(program)?.generate_abi_meta()?)
}
