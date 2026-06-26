mod backend;
#[cfg(not(target_arch = "wasm32"))]
mod dynamic;
mod loaders;
#[cfg(target_arch = "wasm32")]
mod wasm;

use std::io::Write;

#[cfg(not(target_arch = "wasm32"))]
use std::path::Path;

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitIter, BitWriter, Cmr, Cost,
};

use crate::ast::JetHinter;
use crate::jet::{JetHL, SourceJetClassification, TargetJetClassification};
use crate::parse::ParseFromStr;
use crate::types::AliasedType;

use self::backend::ExternalJetLib;
#[cfg(not(target_arch = "wasm32"))]
use crate::jet::external::{dynamic::ExternalJetDynamicLib, loaders::dynlib::Library};

/// ABI version implemented by external jet hosts and plugins.
pub const EXTERNAL_JET_ABI_VERSION: u32 = 1;

/// Load the external jet library from a dynamic library path on non-wasm targets.
///
/// # Safety
///
/// The caller must ensure that the loaded library exports each of the
/// symbols listed below with signatures matching the corresponding
/// fields of [`ExternalJetLib`]. Calling a function through a
/// mismatched signature is undefined behavior.
#[cfg(not(target_arch = "wasm32"))]
pub unsafe fn init_external_jet_lib(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let library = unsafe { Library::load(Path::new(path))? };
    let api = unsafe { ExternalJetDynamicLib::load(library)? };

    if dynamic::EXTERNAL_JET_DYNAMIC_LIB.set(api).is_err() {
        return Err("Failed to set external jet lib, it may have already been initialized".into());
    }

    Ok(())
}

fn external_jet_lib() -> &'static dyn ExternalJetLib {
    #[cfg(target_arch = "wasm32")]
    {
        wasm::external_jet_lib() as &dyn ExternalJetLib
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        dynamic::EXTERNAL_JET_DYNAMIC_LIB
            .get()
            .expect("External jet lib is not initialized. Please call init_external_jet_lib first.")
            as &dyn ExternalJetLib
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct ExternalJet {
    pub index: u64,
}

impl ExternalJet {
    pub fn new(index: u64) -> Self {
        Self { index }
    }
}

impl Jet for ExternalJet {
    fn cmr(&self) -> Cmr {
        let container = external_jet_lib();
        container.cmr(*self)
    }

    fn source_ty(&self) -> TypeName {
        let container = external_jet_lib();
        container.source_ty(*self)
    }

    fn target_ty(&self) -> TypeName {
        let container = external_jet_lib();
        container.target_ty(*self)
    }

    fn encode(&self, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize> {
        let container = external_jet_lib();
        container.encode(*self, w)
    }

    fn decode<I: Iterator<Item = u8>>(
        _bits: &mut BitIter<I>,
    ) -> Result<Self, simplicity::decode::Error>
    where
        Self: Sized,
    {
        unimplemented!("Decoding is not implemented for ExternalJet for now")
    }

    fn cost(&self) -> Cost {
        let container = external_jet_lib();
        container.cost(*self)
    }

    fn parse(s: &str) -> Result<Self, simplicity::Error>
    where
        Self: Sized,
    {
        let container = external_jet_lib();
        container.parse(s)
    }
}

impl std::fmt::Display for ExternalJet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let container = external_jet_lib();
        let display_str = container.display(*self);
        write!(f, "{}", display_str)
    }
}

impl JetHL for ExternalJet {
    fn source_jet_classification(&self) -> SourceJetClassification {
        let container = external_jet_lib();
        container.source_jet_classification(*self)
    }

    fn target_jet_classification(&self) -> TargetJetClassification {
        let container = external_jet_lib();
        container.target_jet_classification(*self)
    }

    fn is_disabled(&self) -> bool {
        let container = external_jet_lib();
        container.is_disabled(*self)
    }

    fn clone_box(&self) -> Box<dyn JetHL> {
        Box::new(*self)
    }

    fn as_jet(&self) -> &dyn Jet {
        self
    }
}

#[derive(Clone, Debug, Default)]
pub struct ExternalJetHinter;

impl ExternalJetHinter {
    pub fn new() -> Self {
        Self
    }
}

impl JetHinter for ExternalJetHinter {
    fn parse_jet(&self, name: &str) -> Option<Box<dyn JetHL>> {
        let container = external_jet_lib();
        match container.parse(name) {
            Ok(jet) => Some(Box::new(jet)),
            Err(_) => None,
        }
    }

    fn construct_verify(&self) -> Box<dyn JetHL> {
        let container = external_jet_lib();
        let jet = container.verify();
        Box::new(jet)
    }

    fn clone_box(&self) -> Box<dyn JetHinter> {
        Box::new(ExternalJetHinter)
    }

    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
        let container = external_jet_lib();
        container.conjure(jet)
    }
}

/// Serialize a [`SourceJetClassification`] into a portable byte buffer.
///
/// Layout:
/// - 1 tag byte: `0` Unary, `1` Binary, `2` Ternary, `3` Quaternary, `4` Custom.
/// - for `Custom`: a little-endian `u32` element count, then, for each element,
///   a little-endian `u32` byte length followed by the UTF-8 [`Display`] form of
///   the [`AliasedType`].
pub fn serialize_source_jet_classification(classification: &SourceJetClassification) -> Vec<u8> {
    let mut out = Vec::new();
    match classification {
        SourceJetClassification::Unary => out.push(0),
        SourceJetClassification::Binary => out.push(1),
        SourceJetClassification::Ternary => out.push(2),
        SourceJetClassification::Quaternary => out.push(3),
        SourceJetClassification::Custom(types) => {
            out.push(4);
            let count = u32::try_from(types.len())
                .expect("source jet classification cannot contain more than u32::MAX types");
            out.extend_from_slice(&count.to_le_bytes());
            for ty in types {
                write_aliased_type(&mut out, ty);
            }
        }
    }
    out
}

/// Inverse of [`serialize_source_jet_classification`].
///
/// Returns `None` if the buffer is truncated, carries an unknown tag, or holds
/// a type string that fails to parse.
pub fn deserialize_source_jet_classification(bytes: &[u8]) -> Option<SourceJetClassification> {
    let (&tag, mut rest) = bytes.split_first()?;
    match tag {
        0 => Some(SourceJetClassification::Unary),
        1 => Some(SourceJetClassification::Binary),
        2 => Some(SourceJetClassification::Ternary),
        3 => Some(SourceJetClassification::Quaternary),
        4 => {
            let count = usize::try_from(read_u32(&mut rest)?).ok()?;
            let mut types = Vec::with_capacity(count.min(rest.len() / 4));
            for _ in 0..count {
                types.push(read_aliased_type(&mut rest)?);
            }
            Some(SourceJetClassification::Custom(types))
        }
        _ => None,
    }
}

/// Serialize a [`TargetJetClassification`] into a portable byte buffer.
///
/// Layout:
/// - 1 tag byte: `0` Unary, `1` Custom.
/// - for `Custom`: a little-endian `u32` byte length followed by the UTF-8
///   [`Display`] form of the [`AliasedType`].
pub fn serialize_target_jet_classification(classification: &TargetJetClassification) -> Vec<u8> {
    let mut out = Vec::new();
    match classification {
        TargetJetClassification::Unary => out.push(0),
        TargetJetClassification::Custom(ty) => {
            out.push(1);
            write_aliased_type(&mut out, ty);
        }
    }
    out
}

/// Inverse of [`serialize_target_jet_classification`].
///
/// Returns `None` if the buffer is truncated, carries an unknown tag, or holds
/// a type string that fails to parse.
pub fn deserialize_target_jet_classification(bytes: &[u8]) -> Option<TargetJetClassification> {
    let (&tag, mut rest) = bytes.split_first()?;
    match tag {
        0 => Some(TargetJetClassification::Unary),
        1 => Some(TargetJetClassification::Custom(read_aliased_type(
            &mut rest,
        )?)),
        _ => None,
    }
}

fn write_aliased_type(out: &mut Vec<u8>, ty: &AliasedType) {
    let s = ty.to_string();
    let len = u32::try_from(s.len()).expect("aliased type cannot exceed u32::MAX bytes");
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(s.as_bytes());
}

fn read_u32(rest: &mut &[u8]) -> Option<u32> {
    if rest.len() < 4 {
        return None;
    }
    let (head, tail) = rest.split_at(4);
    *rest = tail;
    Some(u32::from_le_bytes(head.try_into().ok()?))
}

fn read_aliased_type(rest: &mut &[u8]) -> Option<AliasedType> {
    let len = usize::try_from(read_u32(rest)?).ok()?;
    if rest.len() < len {
        return None;
    }
    let (head, tail) = rest.split_at(len);
    *rest = tail;
    let s = std::str::from_utf8(head).ok()?;
    AliasedType::parse_from_str(s).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jet::{array, bool, either, list, tuple};
    use crate::types::BuiltinAlias;

    #[test]
    fn source_jet_classification_round_trip() {
        let classification = SourceJetClassification::Custom(vec![
            bool(),
            list(bool(), 4),
            array(bool(), 3),
            either(bool(), bool()),
            tuple([bool(), bool()]),
            BuiltinAlias::Pubkey.into(),
        ]);

        let serialized = serialize_source_jet_classification(&classification);
        assert_eq!(
            deserialize_source_jet_classification(&serialized),
            Some(classification)
        );
    }

    #[test]
    fn target_jet_classification_round_trip() {
        let classification = TargetJetClassification::Custom(BuiltinAlias::Pubkey.into());

        let serialized = serialize_target_jet_classification(&classification);
        assert_eq!(
            deserialize_target_jet_classification(&serialized),
            Some(classification)
        );
    }

    #[test]
    fn source_jet_classification_rejects_unbounded_count() {
        let mut serialized = vec![4];
        serialized.extend_from_slice(&u32::MAX.to_le_bytes());

        assert_eq!(deserialize_source_jet_classification(&serialized), None);
    }
}
