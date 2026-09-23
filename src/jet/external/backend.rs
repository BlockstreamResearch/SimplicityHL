use std::io::Write;

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitWriter, Cmr, Cost,
};

use super::ExternalJet;
use crate::jet::{JetHL, SourceJetClassification, TargetJetClassification};

/// Interface implemented by the platform-specific external jet backends.
pub(super) trait ExternalJetLib {
    fn cmr(&self, jet: ExternalJet) -> Cmr;
    fn source_ty(&self, jet: ExternalJet) -> TypeName;
    fn target_ty(&self, jet: ExternalJet) -> TypeName;
    fn encode(&self, jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>)
        -> std::io::Result<usize>;
    fn cost(&self, jet: ExternalJet) -> Cost;
    fn parse(&self, s: &str) -> Result<ExternalJet, simplicity::Error>;
    fn display(&self, jet: ExternalJet) -> String;

    fn source_jet_classification(&self, jet: ExternalJet) -> SourceJetClassification;
    fn target_jet_classification(&self, jet: ExternalJet) -> TargetJetClassification;
    fn is_disabled(&self, jet: ExternalJet) -> bool;

    fn verify(&self) -> ExternalJet;
    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>>;
}
