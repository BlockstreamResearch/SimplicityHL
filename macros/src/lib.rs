extern crate proc_macro;

use quote::__private::Span;
use std::fmt::Display;
use syn::Expr;

mod codegen;
mod parse;

#[proc_macro]
pub fn include_simf(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match include_simf_impl(input.into()) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

// #[proc_macro]
// pub fn include_simf_source(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
//     match include_simf_source_impl(input.into()) {
//         Ok(ts) => ts.into(),
//         Err(e) => e.to_compile_error().into(),
//     }
// }

fn include_simf_impl(input: proc_macro2::TokenStream) -> syn::Result<proc_macro2::TokenStream> {
    let input = syn::parse2::<Expr>(input)?;

    let simf_content = parse::eval_path_expr(input)?;
    let abi_meta = codegen::compile_program(&simf_content)?;
    let generated = codegen::gen_helpers(simf_content, abi_meta)?;

    Ok(generated)
}

// TODO: implement parsing of a constant
// fn include_simf_source_impl(input: proc_macro2::TokenStream) -> syn::Result<proc_macro2::TokenStream> {
//     let simf_content = if let Ok(item_const) = syn::parse2::<ItemConst>(input.clone()) {
//         parse::eval_const_expr(item_const)?
//     };
//
//     let abi_meta = codegen::compile_program(&simf_content)?;
//     let generated = codegen::gen_helpers(&simf_content, abi_meta)?;
//
//     Ok(generated)
// }

#[inline]
fn convert_error_to_syn<E: Display>(err: E) -> syn::Error {
    syn::Error::new(Span::call_site(), err)
}
