use crate::convert_error_to_syn;
use std::fs::File;
use std::io;
use std::io::{ErrorKind, Read};
use std::path::PathBuf;
use syn::spanned::Spanned;
use syn::{Expr, ExprLit, ItemConst, Lit, LitStr};

pub struct SimfContent {
    pub content: String,
    pub contract_name: String,
}

pub fn eval_path_expr(expr: Expr) -> syn::Result<SimfContent> {
    let str_literal = match expr {
        Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        }) => Ok(s.value()),
        _ => Err(syn::Error::new(expr.span(), "Expected string literal")),
    }?;

    let path = validate_path(str_literal)?;
    extract_content_from_path(&path).map_err(|e| convert_error_to_syn(e))
}

// TODO: come up with an idea of how to parse constant values and evaluate constant values that are passed inside
//  pub const OPTION_SOURCE: &str = include_str!("source_simf/options.simf");
//  include_simf_source!(OPTION_SOURCE);
// pub fn eval_const_expr(const_value: ItemConst) -> syn::Result<SimfContent> {
//     let ItemConst {
//         ident,
//         expr,
//         ..
//     } = const_value;
//
//     let expr = expr.as_ref();
//     let content = match expr {
//         Expr::Lit(ExprLit {
//             lit: Lit::Str(s), ..
//         }) => s.value(),
//         _ => return Err(syn::Error::new(expr.span(), "Expected string literal or include_str! macro")),
//     };
//
//     let contract_name = prepare_contract_name(&ident.to_string());
//
//     Ok(SimfContent {
//         content,
//         contract_name,
//     })
// }

pub fn eval_macro_expr(const_value: ItemConst) -> syn::Result<SimfContent> {
    let ItemConst { ident, expr, .. } = const_value;

    let expr = expr.as_ref();
    let content = match expr {
        Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        }) => s.value(),
        _ => {
            return Err(syn::Error::new(
                expr.span(),
                "Expected string literal or include_str! macro",
            ));
        }
    };

    let contract_name = prepare_contract_name(&ident.to_string());

    Ok(SimfContent {
        content,
        contract_name,
    })
}

#[inline]
pub fn prepare_contract_name(name: &str) -> String {
    name.trim_matches(' ').to_lowercase()
}

// TODO: pass span as input parameter to correctly propagate errors

#[inline]
fn validate_path(literal: String) -> syn::Result<PathBuf> {
    let path = PathBuf::from(literal);
    if is_not_a_file(&path) {
        return Err(convert_error_to_syn(format!(
            "File not found, look path: '{:?}', is file: '{}', canonical: '{:?}'",
            path,
            path.is_file(),
            path.canonicalize()
        )));
    }
    Ok(path)
}

fn extract_content_from_path(path: &PathBuf) -> std::io::Result<SimfContent> {
    let contract_name = {
        let name = path
            .file_prefix()
            .ok_or(io::Error::new(
                ErrorKind::Other,
                format!("No file prefix in file: '{:?}'", path),
            ))?
            .to_string_lossy();
        prepare_contract_name(name.as_ref())
    };

    let mut content = String::new();
    let mut x = File::open(path)?;
    x.read_to_string(&mut content)?;
    Ok(SimfContent {
        content,
        contract_name,
    })
}

#[inline]
fn is_not_a_file(path: &PathBuf) -> bool {
    !path.is_file()
}
