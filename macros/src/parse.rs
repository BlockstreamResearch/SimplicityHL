use crate::convert_error_to_syn;
use std::fs::File;
use std::io;
use std::io::{ErrorKind, Read};
use std::path::PathBuf;
use syn::spanned::Spanned;
use syn::{Expr, ExprLit, Lit};

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

/// Prepares a contract name for use as a Rust module/identifier.
///
/// Converts the input to a valid lowercase Rust identifier by:
/// - Trimming whitespace
/// - Converting to lowercase
/// - Replacing invalid characters with underscores
/// - Ensuring it starts with a letter or underscore (not a digit)
/// - Validating it's not a reserved keyword
///
/// # Returns
/// A valid lowercase Rust identifier, or an error if the name cannot be normalized
///
/// # Examples
/// - `"MyContract"` → `"mycontract"`
/// - `"My-Contract-V2"` → `"my_contract_v2"`
/// - `"123Invalid"` → Error (starts with digit)
/// - `"valid_name"` → `"valid_name"`
pub fn prepare_contract_name(name: &str) -> io::Result<String> {
    let trimmed = name.trim_matches(|c: char| c.is_whitespace());
    if trimmed.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "Contract name cannot be empty",
        ));
    }

    let mut result = trimmed.to_lowercase();

    result = result
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();

    while result.contains("__") {
        result = result.replace("__", "_");
    }

    result = result.trim_matches('_').to_string();

    if result.chars().next().map_or(false, |c| c.is_ascii_digit()) {
        result = format!("_{}", result);
    }

    if is_reserved_keyword(&result) {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("Contract name '{}' is a reserved Rust keyword", result),
        ));
    }

    if !is_valid_rust_identifier(&result) {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("Contract name '{}' is not a valid Rust identifier", result),
        ));
    }

    Ok(result)
}

/// Checks if a string is a valid Rust identifier
#[inline]
fn is_valid_rust_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    let first = s.chars().next().unwrap();
    // First char must be letter or underscore
    if !first.is_alphabetic() && first != '_' {
        return false;
    }

    s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// Checks if a string is a Rust reserved keyword (only checks keywords, not format)
///
/// This function validates against Rust's actual reserved keywords.
/// Valid identifiers like "hello" will return false (not a keyword).#[inline]
fn is_reserved_keyword(s: &str) -> bool {
    syn::parse_str::<syn::Ident>(s).is_err()
}

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
        prepare_contract_name(name.as_ref())?
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
