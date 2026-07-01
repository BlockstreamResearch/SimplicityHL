use std::io::Write;

use std::sync::OnceLock;

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitWriter, Cmr, Cost,
};

use crate::jet::{
    external::{loaders::dynlib::Library, ExternalJet, ExternalJetLib},
    JetHL, SourceJetClassification, TargetJetClassification,
};

pub(super) static EXTERNAL_JET_DYNAMIC_LIB: OnceLock<ExternalJetDynamicLib> = OnceLock::new();

/// Symbol table loaded from an external jet dynamic library.
///
/// Each field is a function pointer resolved from a `#[no_mangle]` export of
/// the same name in the library.
#[derive(Clone)]
pub struct ExternalJetDynamicLib {
    pub cmr: fn(jet: ExternalJet) -> Cmr,
    pub source_ty: fn(jet: ExternalJet) -> TypeName,
    pub target_ty: fn(jet: ExternalJet) -> TypeName,
    pub encode: fn(jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize>,
    pub cost: fn(jet: ExternalJet) -> Cost,
    pub parse: fn(s: &str) -> Result<ExternalJet, simplicity::Error>,
    pub display: fn(jet: ExternalJet) -> String,

    pub source_jet_classification: fn(jet: ExternalJet) -> SourceJetClassification,
    pub target_jet_classification: fn(jet: ExternalJet) -> TargetJetClassification,
    pub is_disabled: fn(jet: ExternalJet) -> bool,

    pub verify: fn() -> ExternalJet,
    pub conjure: fn(jet: &dyn Jet) -> Option<Box<dyn JetHL>>,

    // Keep the library loaded, symbols above are only valid while it lives.
    _library: Library,
}

impl ExternalJetDynamicLib {
    /// Resolve all required symbols from `library`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the loaded library exports each of the
    /// symbols listed below with signatures matching the corresponding
    /// fields of [`ExternalJetLib`]. Calling a function through a
    /// mismatched signature is undefined behavior.
    pub unsafe fn load(library: Library) -> Result<Self, Box<dyn std::error::Error>> {
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

impl ExternalJetLib for ExternalJetDynamicLib {
    fn cmr(&self, jet: ExternalJet) -> Cmr {
        (self.cmr)(jet)
    }

    fn source_ty(&self, jet: ExternalJet) -> TypeName {
        (self.source_ty)(jet)
    }

    fn target_ty(&self, jet: ExternalJet) -> TypeName {
        (self.target_ty)(jet)
    }

    fn encode(
        &self,
        jet: ExternalJet,
        w: &mut BitWriter<&mut dyn Write>,
    ) -> std::io::Result<usize> {
        (self.encode)(jet, w)
    }

    fn cost(&self, jet: ExternalJet) -> Cost {
        (self.cost)(jet)
    }

    fn parse(&self, s: &str) -> Result<ExternalJet, simplicity::Error>
    where
        Self: Sized,
    {
        (self.parse)(s)
    }

    fn display(&self, jet: ExternalJet) -> String {
        (self.display)(jet)
    }

    fn source_jet_classification(&self, jet: ExternalJet) -> SourceJetClassification {
        (self.source_jet_classification)(jet)
    }

    fn target_jet_classification(&self, jet: ExternalJet) -> TargetJetClassification {
        (self.target_jet_classification)(jet)
    }

    fn is_disabled(&self, jet: ExternalJet) -> bool {
        (self.is_disabled)(jet)
    }

    fn verify(&self) -> ExternalJet {
        (self.verify)()
    }

    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
        (self.conjure)(jet)
    }
}
