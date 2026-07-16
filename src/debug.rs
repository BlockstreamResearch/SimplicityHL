use std::collections::HashMap;
use std::sync::Arc;

use either::Either;
use hashes::{sha256, Hash, HashEngine};
use simplicity::{hashes, Cmr};

use crate::error::Span;
use crate::types::ResolvedType;
use crate::value::{StructuralValue, Value};

/// Tracker of SimplicityHL call expressions inside Simplicity target code.
///
/// Tracking happens via CMRs that are inserted into the Simplicity target code.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DebugSymbols(HashMap<Cmr, TrackedCall>);

/// Intermediate representation of tracked SimplicityHL call expressions
/// that is mutable and that lacks information about the source file.
///
/// The struct can be converted to [`DebugSymbols`] by providing the source file.
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub(crate) struct CallTracker {
    next_id: u32,
    map: HashMap<Span, (Cmr, TrackedCallName)>,
}

/// Call expression with a debug symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TrackedCall {
    text: Arc<str>,
    name: TrackedCallName,
}

/// Name of a call expression with a debug symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrackedCallName {
    Assert,
    Panic,
    Jet,
    UnwrapLeft(ResolvedType),
    UnwrapRight(ResolvedType),
    Unwrap,
    Debug(ResolvedType),
}

/// Fallible call expression with runtime input value.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FallibleCall {
    text: Arc<str>,
    name: FallibleCallName,
}

/// Name of a fallible call expression with runtime input value.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum FallibleCallName {
    Assert,
    Panic,
    Jet,
    UnwrapLeft(Value),
    UnwrapRight(Value),
    Unwrap,
}

/// Debug expression with runtime input value.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct DebugValue {
    text: Arc<str>,
    value: Value,
}

impl DebugSymbols {
    /// Insert a tracked call expression.
    /// Use the SimplicityHL source `file` to extract the SimplicityHL text of the expression.
    pub(crate) fn insert(&mut self, span: Span, cmr: Cmr, name: TrackedCallName, file: &str) {
        let text = remove_excess_whitespace(span.to_slice(file).unwrap_or(""));
        let text = text
            .strip_prefix("dbg!(")
            .and_then(|s| s.strip_suffix(")"))
            .unwrap_or(&text);

        self.0.insert(
            cmr,
            TrackedCall {
                text: Arc::from(text),
                name,
            },
        );
    }

    /// Check if the given CMR tracks any call expressions.
    pub fn contains_key(&self, cmr: &Cmr) -> bool {
        self.0.contains_key(cmr)
    }

    /// Get the call expression that is tracked by the given CMR.
    pub fn get(&self, cmr: &Cmr) -> Option<&TrackedCall> {
        self.0.get(cmr)
    }
}

fn remove_excess_whitespace(s: &str) -> String {
    let mut last_was_space = true;
    let is_excess_whitespace = move |c: char| match c {
        ' ' => std::mem::replace(&mut last_was_space, true),
        '\n' => true,
        _ => {
            last_was_space = false;
            false
        }
    };
    s.replace(is_excess_whitespace, "")
}

impl CallTracker {
    /// Track a new function call with the given `span`.
    ///
    /// ## Precondition
    ///
    /// Different function calls have different spans.
    ///
    /// This holds true when the method is called on a real source file.
    /// The precondition might be broken when this method is called on random input.
    pub fn track_call(&mut self, span: Span, name: TrackedCallName) {
        let cmr = self.next_id_cmr();
        let _replaced = self.map.insert(span, (cmr, name));
        self.next_id += 1;
    }

    /// Get the CMR of the tracked function call with the given `span`.
    pub fn get_cmr(&self, span: &Span) -> Option<Cmr> {
        self.map.get(span).map(|x| x.0)
    }

    fn next_id_cmr(&self) -> Cmr {
        let tag_hash = sha256::Hash::hash(b"simfony\x1fdebug\x1f");
        let mut engine = sha256::Hash::engine();
        engine.input(tag_hash.as_ref());
        engine.input(tag_hash.as_ref());
        engine.input(self.next_id.to_be_bytes().as_ref());
        Cmr::from_byte_array(sha256::Hash::from_engine(engine).to_byte_array())
    }

    /// Create debug symbols by attaching information from the source `file`.
    pub fn with_file(&self, file: &str) -> DebugSymbols {
        let mut debug_symbols = DebugSymbols::default();
        for (span, (cmr, name)) in &self.map {
            debug_symbols.insert(*span, *cmr, name.clone(), file);
        }
        debug_symbols
    }
}

impl TrackedCall {
    /// Access the text of the SimplicityHL call expression.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Access the name of the call.
    pub fn name(&self) -> &TrackedCallName {
        &self.name
    }

    /// Supply the Simplicity input value of the call expression at runtime.
    /// Convert the debug call into a fallible call or into a debug value,
    /// depending on the kind of debug symbol.
    ///
    /// Return `None` if the Simplicity input value is of the wrong type,
    /// according to the debug symbol.
    pub fn map_value(&self, value: &StructuralValue) -> Option<Either<FallibleCall, DebugValue>> {
        let name = match self.name() {
            TrackedCallName::Assert => FallibleCallName::Assert,
            TrackedCallName::Panic => FallibleCallName::Panic,
            TrackedCallName::Jet => FallibleCallName::Jet,
            TrackedCallName::UnwrapLeft(ty) => {
                Value::reconstruct(value, ty).map(FallibleCallName::UnwrapLeft)?
            }
            TrackedCallName::UnwrapRight(ty) => {
                Value::reconstruct(value, ty).map(FallibleCallName::UnwrapRight)?
            }
            TrackedCallName::Unwrap => FallibleCallName::Unwrap,
            TrackedCallName::Debug(ty) => {
                return Value::reconstruct(value, ty)
                    .map(|value| DebugValue {
                        text: Arc::clone(&self.text),
                        value,
                    })
                    .map(Either::Right)
            }
        };
        Some(Either::Left(FallibleCall {
            text: Arc::clone(&self.text),
            name,
        }))
    }
}

impl FallibleCall {
    /// Access the SimplicityHL text of the call expression.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Access the name of the call.
    pub fn name(&self) -> &FallibleCallName {
        &self.name
    }
}

impl DebugValue {
    /// Access the SimplicityHL text of the debug expression.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Access the runtime input value.
    pub fn value(&self) -> &Value {
        &self.value
    }
}

#[cfg(feature = "serde")]
mod serde_impl {
    //! JSON form of [`DebugSymbols`]: a map from CMR (hex) to `{text, name}`, with
    //! types carried as their string form (like the ABI), so external tooling can
    //! re-attach the symbols to a program whose nodes it resolves by CMR.

    use std::collections::{BTreeMap, HashMap};
    use std::str::FromStr;
    use std::sync::Arc;

    use serde::de::Error as _;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use simplicity::Cmr;

    use super::{DebugSymbols, TrackedCall, TrackedCallName};
    use crate::parse::ParseFromStr;
    use crate::types::ResolvedType;

    /// Wire form of [`TrackedCallName`]: unit variants as strings, type-carrying
    /// variants as single-key objects holding the type's string form.
    #[derive(Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    enum NameRepr {
        Assert,
        Panic,
        Jet,
        UnwrapLeft(String),
        UnwrapRight(String),
        Unwrap,
        Debug(String),
    }

    #[derive(Serialize, Deserialize)]
    struct CallRepr {
        text: String,
        name: NameRepr,
    }

    impl From<&TrackedCallName> for NameRepr {
        fn from(name: &TrackedCallName) -> Self {
            match name {
                TrackedCallName::Assert => Self::Assert,
                TrackedCallName::Panic => Self::Panic,
                TrackedCallName::Jet => Self::Jet,
                TrackedCallName::UnwrapLeft(ty) => Self::UnwrapLeft(ty.to_string()),
                TrackedCallName::UnwrapRight(ty) => Self::UnwrapRight(ty.to_string()),
                TrackedCallName::Unwrap => Self::Unwrap,
                TrackedCallName::Debug(ty) => Self::Debug(ty.to_string()),
            }
        }
    }

    impl TryFrom<NameRepr> for TrackedCallName {
        type Error = String;

        fn try_from(name: NameRepr) -> Result<Self, Self::Error> {
            let ty = |s: String| {
                ResolvedType::parse_from_str(&s).map_err(|error| format!("type `{s}`: {error}"))
            };
            Ok(match name {
                NameRepr::Assert => Self::Assert,
                NameRepr::Panic => Self::Panic,
                NameRepr::Jet => Self::Jet,
                NameRepr::UnwrapLeft(s) => Self::UnwrapLeft(ty(s)?),
                NameRepr::UnwrapRight(s) => Self::UnwrapRight(ty(s)?),
                NameRepr::Unwrap => Self::Unwrap,
                NameRepr::Debug(s) => Self::Debug(ty(s)?),
            })
        }
    }

    impl Serialize for TrackedCall {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            CallRepr {
                text: self.text.to_string(),
                name: NameRepr::from(&self.name),
            }
            .serialize(serializer)
        }
    }

    impl<'de> Deserialize<'de> for TrackedCall {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let repr = CallRepr::deserialize(deserializer)?;
            Ok(TrackedCall {
                text: Arc::from(repr.text.as_str()),
                name: TrackedCallName::try_from(repr.name).map_err(D::Error::custom)?,
            })
        }
    }

    impl Serialize for DebugSymbols {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            // BTreeMap for deterministic field order in the emitted JSON.
            let map: BTreeMap<String, &TrackedCall> = self
                .0
                .iter()
                .map(|(cmr, call)| (cmr.to_string(), call))
                .collect();
            map.serialize(serializer)
        }
    }

    impl<'de> Deserialize<'de> for DebugSymbols {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let map = BTreeMap::<String, TrackedCall>::deserialize(deserializer)?;
            let inner = map
                .into_iter()
                .map(|(cmr, call)| {
                    Cmr::from_str(&cmr)
                        .map(|cmr| (cmr, call))
                        .map_err(|error| D::Error::custom(format!("CMR `{cmr}`: {error}")))
                })
                .collect::<Result<HashMap<Cmr, TrackedCall>, D::Error>>()?;
            Ok(DebugSymbols(inner))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::error::Span;

        #[test]
        fn debug_symbols_roundtrip() {
            let file = "assert!(jet::is_zero_32(x)); dbg!(y)";
            let mut symbols = DebugSymbols::default();
            symbols.insert(
                Span::new_in_default_file(0..28),
                Cmr::from_byte_array([1; 32]),
                TrackedCallName::Assert,
                file,
            );
            symbols.insert(
                Span::new_in_default_file(29..36),
                Cmr::from_byte_array([2; 32]),
                TrackedCallName::Debug(ResolvedType::from(crate::types::UIntType::U32)),
                file,
            );

            let json = serde_json::to_string(&symbols).expect("serialize");
            let back: DebugSymbols = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(symbols, back);
        }
    }
}
