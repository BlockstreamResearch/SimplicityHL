//! Types for handling strings with invariants.

use std::sync::Arc;

/// Implementations for newtypes that wrap [`Arc<str>`].
macro_rules! wrapped_string {
    ($wrapper:ident, $name:expr) => {
        impl $wrapper {
            #[doc = "Create a"]
            #[doc = $name]
            #[doc = ".\n\n"]
            #[doc = "## Precondition\n\n"]
            #[doc = "The string must be a valid"]
            #[doc = $name]
            #[doc = ".\n\n"]
            #[doc = "## Panics\n\n"]
            #[doc = "Panics may occur down the line if the precondition is not satisfied."]
            pub fn from_str_unchecked(s: &str) -> Self {
                Self(Arc::from(s))
            }

            /// Access the inner string.
            pub fn as_inner(&self) -> &str {
                self.0.as_ref()
            }

            /// Make a cheap copy of the name.
            pub fn shallow_clone(&self) -> Self {
                Self(Arc::clone(&self.0))
            }
        }

        impl std::fmt::Display for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }

        impl std::fmt::Debug for $wrapper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

/// Implementation of [`arbitrary::Arbitrary`] for wrapped string types,
/// such that strings of 1 to 10 letters `a` to `z` are generated.
///
/// The space of lowercase letter strings includes reserved keywords,
/// which cannot be used as identifiers. To ensure valid grammar
/// for fuzzing, any generated keywords are padded with the `_`.
macro_rules! impl_arbitrary_lowercase_alpha {
    ($wrapper:ident) => {
        #[cfg(feature = "arbitrary")]
        impl<'a> arbitrary::Arbitrary<'a> for $wrapper {
            fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
                let len = u.int_in_range(1..=10)?;
                let mut string = String::with_capacity(len);
                for _ in 0..len {
                    let offset = u.int_in_range(0..=25)?;
                    string.push((b'a' + offset) as char)
                }
                if crate::lexer::is_keyword(string.as_str()) {
                    string.push('_');
                }
                Ok(Self::from_str_unchecked(string.as_str()))
            }
        }
    };
}

/// The name of a function.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionName(Arc<str>);

impl FunctionName {
    /// Return the name of the main function.
    pub fn main() -> Self {
        Self(Arc::from("main"))
    }
}

wrapped_string!(FunctionName, "function name");

impl Default for FunctionName {
    fn default() -> Self {
        Self(Arc::from(""))
    }
}

impl From<SymbolName> for FunctionName {
    fn from(sym: SymbolName) -> Self {
        // Just move the inner Arc! Zero cost.
        Self(sym.0)
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for FunctionName {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        const RESERVED_NAMES: [&str; 11] = [
            "unwrap_left",
            "unwrap_right",
            "for_while",
            "is_none",
            "unwrap",
            "assert",
            "panic",
            "match",
            "into",
            "fold",
            "dbg",
        ];

        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=25)?;
            string.push((b'a' + offset) as char)
        }
        if RESERVED_NAMES.contains(&string.as_str()) || crate::lexer::is_keyword(string.as_str()) {
            string.push('_');
        }

        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// The identifier of a variable.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Identifier(Arc<str>);

wrapped_string!(Identifier, "variable identifier");
impl_arbitrary_lowercase_alpha!(Identifier);

/// The name of a witness.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct WitnessName(Arc<str>);

wrapped_string!(WitnessName, "witness name");
impl_arbitrary_lowercase_alpha!(WitnessName);

impl AsRef<str> for WitnessName {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

/// The name of a jet.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct JetName(Arc<str>);

wrapped_string!(JetName, "jet name");

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for JetName {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        u.choose(&simplicity::jet::Elements::ALL)
            .map(simplicity::jet::Elements::to_string)
            .map(Arc::from)
            .map(Self)
    }
}

/// The name of a type alias.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct AliasName(Arc<str>);

wrapped_string!(AliasName, "name of a type alias");

impl Default for AliasName {
    fn default() -> Self {
        Self(Arc::from(""))
    }
}

impl From<SymbolName> for AliasName {
    fn from(sym: SymbolName) -> Self {
        Self(sym.0)
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for AliasName {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        const RESERVED_NAMES: [&str; 37] = [
            "Either",
            "Option",
            "bool",
            "List",
            "u128",
            "u256",
            "u16",
            "u32",
            "u64",
            "u1",
            "u2",
            "u4",
            "u8",
            "Ctx8",
            "Pubkey",
            "Message64",
            "Message",
            "Signature",
            "Scalar",
            "Fe",
            "Gej",
            "Ge",
            "Point",
            "Height",
            "Time",
            "Distance",
            "Duration",
            "Lock",
            "Outpoint",
            "Confidential1",
            "ExplicitAsset",
            "Asset1",
            "ExplicitAmount",
            "Amount1",
            "ExplicitNonce",
            "Nonce",
            "TokenAmount1",
        ];

        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=25)?;
            string.push((b'a' + offset) as char)
        }
        if RESERVED_NAMES.contains(&string.as_str()) || crate::lexer::is_keyword(string.as_str()) {
            string.push('_');
        }

        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// A string of decimal digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Decimal(Arc<str>);

wrapped_string!(Decimal, "decimal string");

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Decimal {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=9)?;
            string.push((b'0' + offset) as char)
        }
        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// A string of binary digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Binary(Arc<str>);

wrapped_string!(Binary, "binary string");

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Binary {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=1)?;
            let bin_digit = (b'0' + offset) as char;
            string.push(bin_digit);
        }
        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// A string of hexadecimal digits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Hexadecimal(Arc<str>);

wrapped_string!(Hexadecimal, "hexadecimal string");

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Hexadecimal {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=15)?;
            let hex_digit = match offset {
                0..=9 => (b'0' + offset) as char,
                10..=15 => (b'a' + (offset - 10)) as char,
                _ => unreachable!(),
            };
            string.push(hex_digit);
        }
        Ok(Self::from_str_unchecked(string.as_str()))
    }
}

/// The name of a module.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ModuleName(Arc<str>);

impl ModuleName {
    /// Return the name of the witness module.
    pub fn witness() -> Self {
        Self(Arc::from("witness"))
    }

    /// Return the name of the parameter module.
    pub fn param() -> Self {
        Self(Arc::from("param"))
    }
}

impl From<SymbolName> for ModuleName {
    fn from(sym: SymbolName) -> Self {
        Self(sym.0)
    }
}

wrapped_string!(ModuleName, "module name");

/// An unresolved identifier parsed from the source code.
///
/// During the parsing of `use` statements, the exact kind of the imported
/// item (Function, Alias, or Module) is unknown. This type acts as a
/// temporary placeholder until the name can be fully resolved in later stages.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SymbolName(Arc<str>);

wrapped_string!(SymbolName, "unresolved symbol name");
impl_arbitrary_lowercase_alpha!(SymbolName);

#[cfg(test)]
mod tests {
    use super::*;

    impl Identifier {
        pub fn dummy(name: &str) -> Self {
            Self(std::sync::Arc::from(name))
        }
    }
}
