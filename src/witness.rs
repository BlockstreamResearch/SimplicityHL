use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use crate::error::{Error, RichError, WithContent, WithSpan};
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
    /// witnesses will be pruned and which won't be pruned. This check skips unassigned witnesses.
    pub fn is_consistent(&self, witness_types: &WitnessTypes) -> Result<(), Error> {
        for name in self.0.keys() {
            let Some(declared_ty) = witness_types.get(name) else {
                continue;
            };
            let assigned_ty = self.0[name].ty();
            if assigned_ty != declared_ty {
                return Err(Error::WitnessTypeMismatch {
                    name: name.clone(),
                    declared: declared_ty.clone(),
                    assigned: assigned_ty.clone(),
                });
            }
        }

        Ok(())
    }

    /// Return a copy of these witness values with zero values inserted for any witness declared
    /// in `types` that has no assigned value. Witnesses already present are unchanged.
    ///
    /// This is used before populating Simplicity witness nodes: all nodes must be filled, even
    /// those on branches that will be pruned away and never executed.
    pub fn fill_missing(&self, types: &WitnessTypes) -> (Self, HashSet<WitnessName>) {
        let mut map: HashMap<WitnessName, Value> = (*self.0).clone();
        let mut zero_filled = HashSet::new();
        for (name, ty) in types.iter() {
            if !map.contains_key(name) {
                map.insert(name.shallow_clone(), Value::zero(ty));
                zero_filled.insert(name.shallow_clone());
            }
        }
        (Self::from(map), zero_filled)
    }
}

impl ParseFromStr for ResolvedType {
    fn parse_from_str(s: &str) -> Result<Self, RichError> {
        let aliased = AliasedType::parse_from_str(s)?;
        aliased
            .resolve_builtin()
            .map_err(|name| Error::UndefinedAlias { name })
            .with_span(s)
            .with_content(s)
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
    pub fn is_consistent(&self, parameters: &Parameters) -> Result<(), Error> {
        for (name, parameter_ty) in parameters.iter() {
            let argument = self.get(name).ok_or_else(|| Error::ArgumentMissing {
                name: name.shallow_clone(),
            })?;
            if !argument.is_of_type(parameter_ty) {
                return Err(Error::ArgumentTypeMismatch {
                    name: name.clone(),
                    declared: parameter_ty.clone(),
                    assigned: argument.ty().clone(),
                });
            }
        }

        Ok(())
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
    use crate::error::ErrorCollector;
    use crate::parse::ParseFromStr;
    use crate::value::ValueConstructible;
    use crate::{ast, driver, parse, CompiledProgram, ResolvedType, SatisfiedProgram};

    #[test]
    fn witness_reuse() {
        let s = r#"fn main() {
    assert!(jet::eq_32(witness::A, witness::A));
}"#;
        let parse_program = parse::Program::parse_from_str(s).expect("parsing works");

        let mut error_collector = ErrorCollector::new();
        let driver_program = driver::resolve_order::Program::from_parse(
            &parse_program,
            Arc::from(s),
            &mut error_collector,
        )
        .expect("driver works");
        match ast::Program::analyze(&driver_program, Box::new(ElementsJetHinter::new()))
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
                "Witness `A` was declared with type `u32` but its assigned value is of type `u16`",
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
    fn fill_missing_zero_fills_and_tracks_missing_witnesses() {
        let ty = ResolvedType::parse_from_str("u32").unwrap();
        let witness_types = WitnessTypes::from(HashMap::from([
            (WitnessName::from_str_unchecked("A"), ty.clone()),
            (WitnessName::from_str_unchecked("B"), ty.clone()),
            (WitnessName::from_str_unchecked("C"), ty.clone()),
        ]));

        // A is explicitly provided with value zero (same value fill_missing would insert).
        // B and C are not provided at all.
        let provided = WitnessValues::from(HashMap::from([(
            WitnessName::from_str_unchecked("A"),
            Value::u32(0),
        )]));

        let (filled, zero_filled) = provided.fill_missing(&witness_types);

        // Explicitly-provided witnesses must NOT be tracked as zero-filled,
        // even when their value happens to be zero.
        assert!(
            !zero_filled.contains(&WitnessName::from_str_unchecked("A")),
            "A was explicitly provided; must not appear in zero_filled"
        );
        // Missing witnesses must be tracked so check_surviving_witnesses can error.
        assert!(
            zero_filled.contains(&WitnessName::from_str_unchecked("B")),
            "B was not provided; must appear in zero_filled"
        );
        assert!(
            zero_filled.contains(&WitnessName::from_str_unchecked("C")),
            "C was not provided; must appear in zero_filled"
        );
        // All three must now have values in the filled map.
        assert!(filled.get(&WitnessName::from_str_unchecked("A")).is_some());
        assert!(filled.get(&WitnessName::from_str_unchecked("B")).is_some());
        assert!(filled.get(&WitnessName::from_str_unchecked("C")).is_some());
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
