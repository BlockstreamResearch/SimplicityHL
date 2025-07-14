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
