#[cfg(not(target_arch = "wasm32"))]
mod dynamic;
mod loaders;
#[cfg(target_arch = "wasm32")]
mod wasm;

use std::{io::Write, rc::Rc};

#[cfg(not(target_arch = "wasm32"))]
use std::path::Path;

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitIter, BitWriter, Cmr, Cost,
};

use crate::ast::JetHinter;
use crate::jet::{JetHL, SourceJetClassification, TargetJetClassification};

#[cfg(target_arch = "wasm32")]
use crate::jet::external::wasm::ExternalJetWasmLib;
#[cfg(not(target_arch = "wasm32"))]
use crate::jet::external::{dynamic::ExternalJetDynamicLib, loaders::dynlib::Library};

/// Load the external jet library. When compiled for wasm32, the library is loaded
/// from the current environment. When compiled for other targets
/// the library is loaded from the specified path.
///
/// # Safety
///
/// The caller must ensure that the loaded library exports each of the
/// symbols listed below with signatures matching the corresponding
/// fields of [`ExternalJetLib`]. Calling a function through a
/// mismatched signature is undefined behavior.
#[allow(unused_variables)]
pub unsafe fn init_external_jet_lib(path: Option<&str>) -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(target_arch = "wasm32")]
    {
        let api = ExternalJetWasmLib::load();
        if wasm::EXTERNAL_JET_WASM_LIB.set(api).is_err() {
            return Err(
                "Failed to set external jet lib, it may have already been initialized".into(),
            );
        }
        return Ok(());
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        let path = path.ok_or("Path must be provided for non-wasm targets")?;
        let library = unsafe { Library::load(Path::new(path))? };
        let api = unsafe { ExternalJetDynamicLib::load(library)? };

        if dynamic::EXTERNAL_JET_DYNAMIC_LIB.set(api).is_err() {
            return Err(
                "Failed to set external jet lib, it may have already been initialized".into(),
            );
        }

        Ok(())
    }
}

fn external_jet_lib() -> Rc<dyn ExternalJetLib> {
    #[cfg(target_arch = "wasm32")]
    let lib = wasm::EXTERNAL_JET_WASM_LIB
        .get()
        .expect("External jet lib is not initialized. Please call init_external_jet_lib first.");

    #[cfg(not(target_arch = "wasm32"))]
    let lib = dynamic::EXTERNAL_JET_DYNAMIC_LIB
        .get()
        .expect("External jet lib is not initialized. Please call init_external_jet_lib first.");

    Rc::new(lib.clone())
}

/// External jet integration interface.
///
/// It is used by different loadable libraries backend to connect their
/// implementations of required jets.
pub trait ExternalJetLib {
    // Jet methods
    fn cmr(&self, jet: ExternalJet) -> Cmr;
    fn source_ty(&self, jet: ExternalJet) -> TypeName;
    fn target_ty(&self, jet: ExternalJet) -> TypeName;
    fn encode(&self, jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>)
        -> std::io::Result<usize>;
    fn cost(&self, jet: ExternalJet) -> Cost;
    fn parse(&self, s: &str) -> Result<ExternalJet, simplicity::Error>;
    fn display(&self, jet: ExternalJet) -> String;

    // JetHL methods
    fn source_jet_classification(&self, jet: ExternalJet) -> SourceJetClassification;
    fn target_jet_classification(&self, jet: ExternalJet) -> TargetJetClassification;
    fn is_disabled(&self, jet: ExternalJet) -> bool;

    // JetHinter methods
    fn verify(&self) -> ExternalJet;
    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>>;
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
