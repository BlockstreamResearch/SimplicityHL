use std::sync::OnceLock;
use std::{io::Write, path::Path};

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitIter, BitWriter, Cmr, Cost,
};

use crate::ast::JetHinter;
use crate::jet::dynlib::Library;
use crate::jet::{JetHL, SourceJetClassification, TargetJetClassification};

static EXTERNAL_JET_LIB: OnceLock<ExternalJetLib> = OnceLock::new();

/// Load the external jet library from the specified shared object file path
///
/// # Safety
///
/// The caller must ensure that the loaded library exports each of the
/// symbols listed below with signatures matching the corresponding
/// fields of [`ExternalJetLib`]. Calling a function through a
/// mismatched signature is undefined behavior.
pub unsafe fn init_external_jet_lib(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let library = unsafe { Library::load(Path::new(path))? };
    let api = unsafe { ExternalJetLib::load(library)? };

    if EXTERNAL_JET_LIB.set(api).is_err() {
        return Err("Failed to set external jet lib, it may have already been initialized".into());
    }

    Ok(())
}

fn external_jet_lib() -> &'static ExternalJetLib {
    EXTERNAL_JET_LIB
        .get()
        .expect("External jet lib is not initialized. Please call init_external_jet_lib first.")
}

/// Symbol table loaded from an external jet shared library.
///
/// Each field is a function pointer resolved from a `#[no_mangle]` export of
/// the same name in the library.
pub struct ExternalJetLib {
    cmr: fn(jet: ExternalJet) -> Cmr,
    source_ty: fn(jet: ExternalJet) -> TypeName,
    target_ty: fn(jet: ExternalJet) -> TypeName,
    encode: fn(jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize>,
    cost: fn(jet: ExternalJet) -> Cost,
    parse: fn(s: &str) -> Result<ExternalJet, simplicity::Error>,
    display: fn(jet: ExternalJet) -> String,

    source_jet_classification: fn(jet: ExternalJet) -> SourceJetClassification,
    target_jet_classification: fn(jet: ExternalJet) -> TargetJetClassification,
    is_disabled: fn(jet: ExternalJet) -> bool,

    verify: fn() -> ExternalJet,
    conjure: fn(jet: &dyn Jet) -> Option<Box<dyn JetHL>>,

    // Keep the library loaded, symbols above are only valid while it lives.
    _library: Library,
}

impl ExternalJetLib {
    /// Resolve all required symbols from `library`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the loaded library exports each of the
    /// symbols listed below with signatures matching the corresponding
    /// fields of [`ExternalJetLib`]. Calling a function through a
    /// mismatched signature is undefined behavior.
    unsafe fn load(library: Library) -> Result<Self, Box<dyn std::error::Error>> {
        let cmr = library.symbol("cmr")?;
        let source_ty = library.symbol("source_ty")?;
        let target_ty = library.symbol("target_ty")?;
        let encode = library.symbol("encode")?;
        let cost = library.symbol("cost")?;
        let parse = library.symbol("parse")?;
        let display = library.symbol("display")?;
        let source_jet_classification = library.symbol("source_jet_classification")?;
        let target_jet_classification = library.symbol("target_jet_classification")?;
        let is_disabled = library.symbol("is_disabled")?;
        let verify = library.symbol("verify")?;
        let conjure = library.symbol("conjure")?;

        Ok(Self {
            cmr,
            source_ty,
            target_ty,
            encode,
            cost,
            parse,
            display,
            source_jet_classification,
            target_jet_classification,
            is_disabled,
            verify,
            conjure,
            _library: library,
        })
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
        (container.cmr)(*self)
    }

    fn source_ty(&self) -> TypeName {
        let container = external_jet_lib();
        (container.source_ty)(*self)
    }

    fn target_ty(&self) -> TypeName {
        let container = external_jet_lib();
        (container.target_ty)(*self)
    }

    fn encode(&self, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize> {
        let container = external_jet_lib();
        (container.encode)(*self, w)
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
        (container.cost)(*self)
    }

    fn parse(s: &str) -> Result<Self, simplicity::Error>
    where
        Self: Sized,
    {
        let container = external_jet_lib();
        (container.parse)(s)
    }
}

impl std::fmt::Display for ExternalJet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let container = external_jet_lib();
        let display_str = (container.display)(*self);
        write!(f, "{}", display_str)
    }
}

impl JetHL for ExternalJet {
    fn source_jet_classification(&self) -> SourceJetClassification {
        let container = external_jet_lib();
        (container.source_jet_classification)(*self)
    }

    fn target_jet_classification(&self) -> TargetJetClassification {
        let container = external_jet_lib();
        (container.target_jet_classification)(*self)
    }

    fn is_disabled(&self) -> bool {
        let container = external_jet_lib();
        (container.is_disabled)(*self)
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
        match (container.parse)(name) {
            Ok(jet) => Some(Box::new(jet)),
            Err(_) => None,
        }
    }

    fn construct_verify(&self) -> Box<dyn JetHL> {
        let container = external_jet_lib();
        let jet = (container.verify)();
        Box::new(jet)
    }

    fn clone_box(&self) -> Box<dyn JetHinter> {
        Box::new(ExternalJetHinter)
    }

    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
        let container = external_jet_lib();
        (container.conjure)(jet)
    }
}
