use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::error::{Diagnostic, DiagnosticManager, Error, WithSpan};
use crate::parse::ParseFromStr;
use crate::str::WitnessName;
use crate::types::{AliasedType, ResolvedType};
use crate::value::Value;

macro_rules! impl_name_type_map {
    ($wrapper: ident) => {
        impl $wrapper {
            /// Get the type that is assigned to the given name.
            pub fn get(&self, name: &WitnessName) -> Option<&ResolvedType> {
                self.0.get(name)
            }

            /// Create an iterator over all name-type pairs.
            pub fn iter(&self) -> impl Iterator<Item = (&WitnessName, &ResolvedType)> {
                self.0.iter()
            }

            /// Make a cheap copy of the map.
            pub fn shallow_clone(&self) -> Self {
                Self(Arc::clone(&self.0))
            }
        }

        impl From<HashMap<WitnessName, ResolvedType>> for $wrapper {
            fn from(value: HashMap<WitnessName, ResolvedType>) -> Self {
                Self(Arc::new(value))
            }
        }
    };
}

macro_rules! impl_name_value_map {
    ($wrapper: ident, $module_name: expr) => {
        impl $wrapper {
            /// Access the inner map.
            #[cfg(feature = "serde")]
            pub(crate) fn as_inner(&self) -> &HashMap<WitnessName, Value> {
                &self.0
            }

            /// Get the value that is assigned to the given name.
            pub fn get(&self, name: &WitnessName) -> Option<&Value> {
                self.0.get(name)
            }

            /// Create an iterator over all name-value pairs.
            pub fn iter(&self) -> impl Iterator<Item = (&WitnessName, &Value)> {
                self.0.iter()
            }

            /// Make a cheap copy of the map.
            pub fn shallow_clone(&self) -> Self {
                Self(Arc::clone(&self.0))
            }
        }

        impl From<HashMap<WitnessName, Value>> for $wrapper {
            fn from(value: HashMap<WitnessName, Value>) -> Self {
                Self(Arc::new(value))
            }
        }

        impl fmt::Display for $wrapper {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                use itertools::Itertools;

                writeln!(f, "mod {} {{", $module_name)?;
                for name in self.0.keys().sorted_unstable() {
                    let value = self.0.get(name).unwrap();
                    writeln!(f, "    const {name}: {} = {value};", value.ty())?;
                }
                write!(f, "}}")
            }
        }
    };
}

/// Map of witness types.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct WitnessTypes(Arc<HashMap<WitnessName, ResolvedType>>);

impl_name_type_map!(WitnessTypes);

impl AsRef<HashMap<WitnessName, ResolvedType>> for WitnessTypes {
    fn as_ref(&self) -> &HashMap<WitnessName, ResolvedType> {
        self.0.as_ref()
    }
}

/// Map of witness values.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct WitnessValues(Arc<HashMap<WitnessName, Value>>);

impl_name_value_map!(WitnessValues, "witness");

impl WitnessValues {
    /// Check if the witness values are consistent with the declared witness types.
    ///
    /// 1. Values that occur in the program are type checked.
    /// 2. Values that don't occur in the program are skipped.
    ///    The witness map may contain more values than necessary.
    ///
    /// There may be witnesses that are referenced in the program that are not assigned a value
    /// in the witness map. These witnesses may lie on pruned branches that will not be part of the
    /// finalized Simplicity program. However, before the finalization, we cannot know which
    /// witnesses will be pruned and which won't be pruned.
    pub fn is_consistent(&self, witness_types: &WitnessTypes, diagnostics: &mut DiagnosticManager) {
        for (name, declared_ty) in witness_types.iter() {
            let Some(value) = self.get(name) else {
                diagnostics.push(Diagnostic::global(Error::WitnessMissing {
                    name: name.shallow_clone(),
                }));
                continue;
            };

            let assigned_ty = value.ty();
            if assigned_ty != declared_ty {
                diagnostics.push(Diagnostic::global(Error::WitnessTypeMismatch {
                    name: name.clone(),
                    declared: declared_ty.clone(),
                    assigned: assigned_ty.clone(),
                }));
            }
        }
    }
}

/// A value from a witness or argument file whose type may come from the program.
#[cfg(feature = "serde")]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UnresolvedValue {
    /// A bare value string (`"NAME": "42"`), parsed against the type
    /// that the program declares for `NAME`.
    Untyped(String),
    /// A self-typed entry (`"NAME": { "value": "42", "type": "u32" }`),
    /// parsed against the type written in the file.
    Typed(Value),
}

/// Witness or argument values parsed from a file, before their types are resolved
/// against the program.
///
/// See docs Untyped and Typed variants of `UnresolvedValue` enum to understand how entries are resolved.
///
/// Call [`UnresolvedValues::resolve`] with the program's declared types to obtain
/// [`WitnessValues`] or [`Arguments`].
#[cfg(feature = "serde")]
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct UnresolvedValues(HashMap<WitnessName, UnresolvedValue>);

#[cfg(feature = "serde")]
impl UnresolvedValues {
    pub(crate) fn from_map(map: HashMap<WitnessName, UnresolvedValue>) -> Self {
        Self(map)
    }

    /// Resolve each value against the type that the program declares for its name.
    ///
    /// ## Errors
    ///
    /// - A bare value string is given for a name that the program does not declare.
    /// - A bare value string does not parse at the declared type.
    ///
    /// Self-typed entries are passed through unchanged.
    /// They are type-checked against the program later, when the program is instantiated/satisfied.
    pub fn resolve<T, M>(self, declared_types: &M) -> Result<T, String>
    where
        T: From<HashMap<WitnessName, Value>>,
        M: AsRef<HashMap<WitnessName, ResolvedType>>,
    {
        let declared_types = declared_types.as_ref();
        let mut map = HashMap::with_capacity(self.0.len());
        for (name, unresolved) in self.0 {
            let value = match unresolved {
                UnresolvedValue::Typed(value) => value,
                UnresolvedValue::Untyped(s) => {
                    let ty = declared_types.get(&name).ok_or_else(|| {
                        format!("`{name}` is not declared by the program, so its value `{s}` cannot be assigned a type")
                    })?;
                    Value::parse_from_str(&s, ty)
                        .map_err(|error| format!("`{name}` is declared as `{ty}`: {error}"))?
                }
            };
            map.insert(name, value);
        }
        Ok(T::from(map))
    }
}

impl ParseFromStr for ResolvedType {
    fn parse_from_str(s: &str) -> Result<Self, Diagnostic> {
        let aliased = AliasedType::parse_from_str(s)?;
        aliased
            .resolve_builtin()
            .map_err(|name| Error::UndefinedAlias { name })
            .with_span(s)
    }
}

/// Map of parameters.
///
/// A parameter is a named variable that resolves to a value of a given type.
/// Parameters have a name and a type.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct Parameters(Arc<HashMap<WitnessName, ResolvedType>>);

impl_name_type_map!(Parameters);

impl AsRef<HashMap<WitnessName, ResolvedType>> for Parameters {
    fn as_ref(&self) -> &HashMap<WitnessName, ResolvedType> {
        self.0.as_ref()
    }
}

/// Map of arguments.
///
/// An argument is the value of a parameter.
/// Arguments have a name and a value of a given type.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Arguments(Arc<HashMap<WitnessName, Value>>);

impl_name_value_map!(Arguments, "param");

impl Arguments {
    /// Check if the arguments are consistent with the given parameters.
    ///
    /// 1. Each parameter must be supplied with an argument.
    /// 2. The type of each parameter must match the type of its argument.
    ///
    /// Arguments without a corresponding parameter are ignored.
    pub fn is_consistent(&self, parameters: &Parameters, diagnostics: &mut DiagnosticManager) {
        for (name, parameter_ty) in parameters.iter() {
            let Some(argument) = self.get(name) else {
                diagnostics.push(Diagnostic::global(Error::ArgumentMissing {
                    name: name.shallow_clone(),
                }));
                continue;
            };

            if !argument.is_of_type(parameter_ty) {
                diagnostics.push(Diagnostic::global(Error::ArgumentTypeMismatch {
                    name: name.clone(),
                    declared: parameter_ty.clone(),
                    assigned: argument.ty().clone(),
                }));
            }
        }
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryOfType for Arguments {
    type Type = Parameters;

    fn arbitrary_of_type(
        u: &mut arbitrary::Unstructured,
        ty: &Self::Type,
    ) -> arbitrary::Result<Self> {
        let mut map = HashMap::new();
        for (name, parameter_ty) in ty.iter() {
            map.insert(
                name.shallow_clone(),
                Value::arbitrary_of_type(u, parameter_ty)?,
            );
        }
        Ok(Self::from(map))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ElementsJetHinter;
    use crate::parse::ParseFromStr;
    use crate::value::ValueConstructible;
    use crate::{ast, parse, CompiledProgram, SatisfiedProgram};

    #[test]
    fn witness_reuse() {
        let s = r#"fn main() {
    assert!(jet::eq_32(witness::A, witness::A));
}"#;
        let parse_program = parse::Program::parse_from_str(s).expect("parsing works");
        match ast::Program::analyze(&parse_program, Box::new(ElementsJetHinter::new()))
            .map_err(Error::from)
        {
            Ok(_) => panic!("Witness reuse was falsely accepted"),
            Err(Error::WitnessReused { .. }) => {}
            Err(error) => panic!("Unexpected error: {error}"),
        }
    }

    #[test]
    fn witness_type_mismatch() {
        let s = r#"fn main() {
    assert!(jet::is_zero_32(witness::A));
}"#;

        let witness = WitnessValues::from(HashMap::from([(
            WitnessName::from_str_unchecked("A"),
            Value::u16(42),
        )]));
        match SatisfiedProgram::new(
            s,
            Arguments::default(),
            witness,
            false,
            Box::new(ElementsJetHinter::new()),
        ) {
            Ok(_) => panic!("Ill-typed witness assignment was falsely accepted"),
            Err(error) => assert_eq!(
                "Witness `A` was declared with type `u32` but its assigned value is of type `u16`\n",
                error
            ),
        }
    }

    #[test]
    fn witness_outside_main() {
        let s = r#"fn f() -> u32 {
    witness::OUTPUT_OF_F
}

fn main() {
    assert!(jet::is_zero_32(f()));
}"#;

        match CompiledProgram::new(
            s,
            Arguments::default(),
            false,
            Box::new(ElementsJetHinter::new()),
        ) {
            Ok(_) => panic!("Witness outside main was falsely accepted"),
            Err(error) => {
                assert!(error
                    .contains("Witness expressions are not allowed outside the `main` function"))
            }
        }
    }

    #[test]
    #[cfg(feature = "serde")]
    fn unresolved_values_resolve_against_declared_types() {
        let u32_ty = ResolvedType::parse_from_str("u32").unwrap();
        let sig_ty = ResolvedType::parse_from_str("Signature").unwrap();
        let witness_types = WitnessTypes::from(HashMap::from([
            (WitnessName::from_str_unchecked("A"), u32_ty.clone()),
            (WitnessName::from_str_unchecked("SIG"), sig_ty),
        ]));

        let unresolved = UnresolvedValues::from_map(HashMap::from([
            (
                WitnessName::from_str_unchecked("A"),
                UnresolvedValue::Untyped("42".to_string()),
            ),
            (
                WitnessName::from_str_unchecked("B"),
                UnresolvedValue::Typed(Value::u16(7)),
            ),
        ]));
        let resolved: WitnessValues = unresolved.resolve(&witness_types).unwrap();
        assert_eq!(
            resolved.get(&WitnessName::from_str_unchecked("A")),
            Some(&Value::u32(42))
        );
        assert_eq!(
            resolved.get(&WitnessName::from_str_unchecked("B")),
            Some(&Value::u16(7))
        );

        let unknown = UnresolvedValues::from_map(HashMap::from([(
            WitnessName::from_str_unchecked("TYPO"),
            UnresolvedValue::Untyped("1".to_string()),
        )]));
        let err = unknown
            .resolve::<WitnessValues, _>(&witness_types)
            .unwrap_err();
        assert!(err.contains("TYPO"), "error should name the entry: {err}");

        let bad = UnresolvedValues::from_map(HashMap::from([(
            WitnessName::from_str_unchecked("A"),
            UnresolvedValue::Untyped("not-a-number".to_string()),
        )]));
        let err = bad.resolve::<WitnessValues, _>(&witness_types).unwrap_err();
        assert!(
            err.contains('A') && err.contains("u32"),
            "error should name the witness and its declared type: {err}"
        );
    }

    #[test]
    #[cfg(feature = "serde")]
    fn unresolved_values_parse_from_json() {
        // Bare strings and legacy value/type maps may be mixed in one file.
        let s = r#"{
  "A": "42",
  "B": { "value": "7", "type": "u16" }
}"#;
        let unresolved: UnresolvedValues = serde_json::from_str(s).unwrap();
        let u32_ty = ResolvedType::parse_from_str("u32").unwrap();
        let witness_types = WitnessTypes::from(HashMap::from([(
            WitnessName::from_str_unchecked("A"),
            u32_ty,
        )]));
        let resolved: WitnessValues = unresolved.resolve(&witness_types).unwrap();
        assert_eq!(
            resolved.get(&WitnessName::from_str_unchecked("A")),
            Some(&Value::u32(42))
        );
        assert_eq!(
            resolved.get(&WitnessName::from_str_unchecked("B")),
            Some(&Value::u16(7))
        );

        // Duplicate names are rejected at parse time, as for WitnessValues.
        let dup = r#"{ "A": "1", "A": "2" }"#;
        assert!(serde_json::from_str::<UnresolvedValues>(dup).is_err());
    }

    #[test]
    fn witness_to_string() {
        let witness = WitnessValues::from(HashMap::from([
            (WitnessName::from_str_unchecked("A"), Value::u32(1)),
            (WitnessName::from_str_unchecked("B"), Value::u32(2)),
            (WitnessName::from_str_unchecked("C"), Value::u32(3)),
        ]));
        let expected_string = r#"mod witness {
    const A: u32 = 1;
    const B: u32 = 2;
    const C: u32 = 3;
}"#;
        assert_eq!(expected_string, witness.to_string());
    }
}
