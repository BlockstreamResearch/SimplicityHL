use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use simplicity::Cmr;

use crate::error::{RichError, WithContent as _};
use crate::types::{ResolvedType, TypeInner, UIntType};
use crate::value::{Value, ValueConstructible};
use crate::{named, Arguments, Parameters, TemplateProgram};

/// Canonical identifier for a SimplicityHL contract template.
///
/// The identifier is the CMR of the template compiled with every parameter set
/// to the zero value of its declared type and debug symbols disabled.
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct ContractId(Cmr);

impl ContractId {
    /// Compute the contract ID for the given template.
    ///
    /// The contract ID is the CMR of the template compiled with every parameter
    /// set to the zero value of its declared type.
    ///
    /// Debug symbols are disabled during the compilation.
    ///
    /// ## Errors
    ///
    /// Returns an error if program compilation fails.
    pub fn from_template(template: &TemplateProgram) -> Result<Self, RichError> {
        let arguments = zero_arguments(template.parameters());
        let commit = template
            .simfony
            .compile(arguments, false, template.jet_hinter.clone_box())
            .with_content(Arc::clone(&template.file))?;
        Ok(Self(named::forget_names(&commit).cmr()))
    }

    /// Access the underlying CMR.
    pub fn cmr(self) -> Cmr {
        self.0
    }
}

impl fmt::Display for ContractId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

fn zero_arguments(parameters: &Parameters) -> Arguments {
    let map = parameters
        .iter()
        .map(|(name, ty)| (name.shallow_clone(), zero_value(ty)))
        .collect::<HashMap<_, _>>();
    Arguments::from(map)
}

fn zero_value(ty: &ResolvedType) -> Value {
    match ty.as_inner() {
        TypeInner::Either(left, right) => Value::left(zero_value(left), right.as_ref().clone()),
        TypeInner::Option(inner) => Value::none(inner.as_ref().clone()),
        TypeInner::Boolean => Value::from(false),
        TypeInner::UInt(uint) => zero_uint(*uint),
        TypeInner::Tuple(elements) => Value::tuple(elements.iter().map(|ty| zero_value(ty))),
        TypeInner::Array(element, size) => {
            let elements = std::iter::repeat_with(|| zero_value(element)).take(*size);
            Value::array(elements, element.as_ref().clone())
        }
        TypeInner::List(element, bound) => Value::list([], element.as_ref().clone(), *bound),
    }
}

fn zero_uint(ty: UIntType) -> Value {
    match ty {
        UIntType::U1 => Value::u1(0),
        UIntType::U2 => Value::u2(0),
        UIntType::U4 => Value::u4(0),
        UIntType::U8 => Value::u8(0),
        UIntType::U16 => Value::u16(0),
        UIntType::U32 => Value::u32(0),
        UIntType::U64 => Value::u64(0),
        UIntType::U128 => Value::u128(0),
        UIntType::U256 => Value::u256(crate::num::U256::MIN),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::ast::ElementsJetHinter;
    use crate::str::WitnessName;
    use crate::types::TypeConstructible;
    use crate::value::ValueConstructible;
    use crate::{Arguments, ResolvedType, TemplateProgram, Value};

    #[test]
    fn contract_id_matches_zero_argument_cmr() {
        let code = "fn main() { assert!(jet::eq_32(param::N, param::N)); }";
        let template = TemplateProgram::new(code, Box::new(ElementsJetHinter::new())).unwrap();
        let zero_arguments = Arguments::from(HashMap::from([(
            WitnessName::from_str_unchecked("N"),
            Value::u32(0),
        )]));

        let contract_id = template.contract_id().unwrap();
        let zero_cmr = template
            .instantiate(zero_arguments, false)
            .unwrap()
            .commit()
            .cmr();

        assert_eq!(contract_id.cmr(), zero_cmr);
    }

    #[test]
    fn contract_id_for_non_parameterized_program_is_normal_cmr() {
        let code = "fn main() { assert!(true); }";
        let template = TemplateProgram::new(code, Box::new(ElementsJetHinter::new())).unwrap();
        let compiled = template.instantiate(Arguments::default(), false).unwrap();

        assert_eq!(
            template.contract_id().unwrap().cmr(),
            compiled.commit().cmr()
        );
    }

    #[test]
    fn contract_id_zeroes_composite_parameters() {
        let code = r#"fn main() {
    let pair: (u8, bool) = param::PAIR;
    let bytes: [u8; 2] = param::BYTES;
    let maybe: Option<u16> = param::MAYBE;
    let items: List<u8, 4> = param::ITEMS;
    assert!(true);
}"#;
        let template = TemplateProgram::new(code, Box::new(ElementsJetHinter::new())).unwrap();
        let zero_arguments = Arguments::from(HashMap::from([
            (
                WitnessName::from_str_unchecked("PAIR"),
                Value::tuple([Value::u8(0), Value::from(false)]),
            ),
            (
                WitnessName::from_str_unchecked("BYTES"),
                Value::array([Value::u8(0), Value::u8(0)], ResolvedType::u8()),
            ),
            (
                WitnessName::from_str_unchecked("MAYBE"),
                Value::none(ResolvedType::u16()),
            ),
            (
                WitnessName::from_str_unchecked("ITEMS"),
                Value::list(
                    [],
                    ResolvedType::u8(),
                    crate::num::NonZeroPow2Usize::new(4).unwrap(),
                ),
            ),
        ]));

        let contract_id = template.contract_id().unwrap();
        let zero_cmr = template
            .instantiate(zero_arguments, false)
            .unwrap()
            .commit()
            .cmr();

        assert_eq!(contract_id.cmr(), zero_cmr);
    }
}
