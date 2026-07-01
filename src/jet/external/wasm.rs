#![cfg(target_arch = "wasm32")]

use std::io::Write;
use std::sync::OnceLock;

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitWriter, Cmr, Cost,
};

use crate::jet::{
    external::{ExternalJet, ExternalJetLib},
    JetHL, SourceJetClassification, TargetJetClassification,
};

/// External jet backend for `wasm32` builds.
///
/// All methods are imported from the `simplicityhl-plugin` wasm module,
/// which the embedding host (e.g. a browser) provides.
#[derive(Clone, Debug, Default)]
pub struct ExternalJetWasmLib;

pub(crate) static EXTERNAL_JET_WASM_LIB: OnceLock<ExternalJetWasmLib> = OnceLock::new();

impl ExternalJetWasmLib {
    pub fn load() -> Self {
        Self
    }
}

#[link(wasm_import_module = "simplicityhl-plugin")]
#[allow(improper_ctypes)]
extern "C" {
    fn cmr(jet: ExternalJet) -> Cmr;
    fn source_ty(jet: ExternalJet) -> TypeName;
    fn target_ty(jet: ExternalJet) -> TypeName;
    fn encode(jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize>;
    fn cost(jet: ExternalJet) -> Cost;
    fn parse(name_ptr: *const u8, name_len: usize, out: *mut ExternalJet) -> i32;
    fn display(jet: ExternalJet) -> String;
    fn source_jet_classification(jet: ExternalJet) -> SourceJetClassification;
    fn target_jet_classification(jet: ExternalJet) -> TargetJetClassification;
    fn is_disabled(jet: ExternalJet) -> bool;
    fn verify() -> ExternalJet;
}

impl ExternalJetLib for ExternalJetWasmLib {
    fn cmr(&self, jet: ExternalJet) -> Cmr {
        unsafe { cmr(jet) }
    }

    fn source_ty(&self, jet: ExternalJet) -> TypeName {
        unsafe { source_ty(jet) }
    }

    fn target_ty(&self, jet: ExternalJet) -> TypeName {
        unsafe { target_ty(jet) }
    }

    fn encode(
        &self,
        jet: ExternalJet,
        w: &mut BitWriter<&mut dyn Write>,
    ) -> std::io::Result<usize> {
        unsafe { encode(jet, w) }
    }

    fn cost(&self, jet: ExternalJet) -> Cost {
        unsafe { cost(jet) }
    }

    fn parse(&self, s: &str) -> Result<ExternalJet, simplicity::Error> {
        let mut jet = ExternalJet::new(0);
        let status = unsafe { parse(s.as_ptr(), s.len(), &mut jet) };
        if status == 0 {
            Ok(jet)
        } else {
            Err(simplicity::Error::InvalidJetName(s.to_owned()))
        }
    }

    fn display(&self, jet: ExternalJet) -> String {
        unsafe { display(jet) }
    }

    fn source_jet_classification(&self, jet: ExternalJet) -> SourceJetClassification {
        unsafe { source_jet_classification(jet) }
    }

    fn target_jet_classification(&self, jet: ExternalJet) -> TargetJetClassification {
        unsafe { target_jet_classification(jet) }
    }

    fn is_disabled(&self, jet: ExternalJet) -> bool {
        unsafe { is_disabled(jet) }
    }

    fn verify(&self) -> ExternalJet {
        unsafe { verify() }
    }

    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
        jet.as_any()
            .downcast_ref::<ExternalJet>()
            .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
    }
}
