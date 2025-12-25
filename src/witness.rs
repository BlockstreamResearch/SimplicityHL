use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::error::{Error, RichError, WithFile, WithSpan};
use crate::parse;
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

        impl ParseFromStr for $wrapper {
            fn parse_from_str(s: &str) -> Result<Self, RichError> {
                parse::ModuleProgram::parse_from_str(s).and_then(|x| Self::analyze(&x))
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
                return Err(Error::WitnessTypeMismatch(
                    name.clone(),
                    declared_ty.clone(),
                    assigned_ty.clone(),
                ));
            }
        }

        Ok(())
    }
}

impl ParseFromStr for ResolvedType {
    fn parse_from_str(s: &str) -> Result<Self, RichError> {
        let aliased = AliasedType::parse_from_str(s)?;
        aliased
            .resolve_builtin()
            .map_err(Error::UndefinedAlias)
            .with_span(s)
            .with_file(s)
    }
}

/// Map of parameters.
///
/// A parameter is a named variable that resolves to a value of a given type.
/// Parameters have a name and a type.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct Parameters(Arc<HashMap<WitnessName, ResolvedType>>);

impl_name_type_map!(Parameters);

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
            let argument = self
                .get(name)
                .ok_or_else(|| Error::ArgumentMissing(name.shallow_clone()))?;
            if !argument.is_of_type(parameter_ty) {
                return Err(Error::ArgumentTypeMismatch(
                    name.clone(),
                    parameter_ty.clone(),
                    argument.ty().clone(),
                ));
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
    use crate::parse::ParseFromStr;
    use crate::value::ValueConstructible;
    use crate::{ast, parse, CompiledProgram, SatisfiedProgram};

    #[test]
    fn witness_reuse() {
        let s = r#"fn main() {
    assert!(jet::eq_32(witness::A, witness::A));
}"#;
        let program = parse::Program::parse_from_str(s).expect("parsing works");
        match ast::Program::analyze(&program).map_err(Error::from) {
            Ok(_) => panic!("Witness reuse was falsely accepted"),
            Err(Error::WitnessReused(..)) => {}
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
        match SatisfiedProgram::new(s, Arguments::default(), witness, false) {
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

        match CompiledProgram::new(s, Arguments::default(), false) {
            Ok(_) => panic!("Witness outside main was falsely accepted"),
            Err(error) => {
                assert!(error
                    .contains("Witness expressions are not allowed outside the `main` function"))
            }
        }
    }

    #[test]
    fn missing_witness_module() {
        match WitnessValues::parse_from_str("") {
            Ok(values) => assert!(values.iter().next().is_none()),
            Err(error) => panic!("Expected empty witness values, but got error: {}", error),
        }
    }

    #[test]
    fn redefined_witness_module() {
        let s = r#"mod witness {} mod witness {}"#;
        match WitnessValues::parse_from_str(s) {
            Ok(_) => panic!("Redefined witness module was falsely accepted"),
            Err(error) => assert!(error
                .to_string()
                .contains("Module `witness` is defined twice")),
        }
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
