use std::io::Write;

use simplicityhl::{
    jet::{JetHL, SourceJetClassification, TargetJetClassification},
    simplicity::{
        jet::{type_name::TypeName, Jet},
        BitWriter, Cmr, Cost,
    },
};

use crate::jet::{ExternalJet, HappyJet};

mod jet;

#[no_mangle]
pub fn cmr(jet: ExternalJet) -> Cmr {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.cmr()
}

#[no_mangle]
pub fn source_ty(jet: ExternalJet) -> TypeName {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.source_ty()
}

#[no_mangle]
pub fn target_ty(jet: ExternalJet) -> TypeName {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.target_ty()
}

#[no_mangle]
pub fn encode(jet: ExternalJet, w: &mut dyn Write) -> std::io::Result<usize> {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    let mut bit_writer = BitWriter::new(w);

    jet.encode(&mut bit_writer)
}

#[no_mangle]
pub fn cost(jet: ExternalJet) -> Cost {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.cost()
}

#[no_mangle]
pub fn parse(s: &str) -> Result<ExternalJet, simplicityhl::simplicity::Error> {
    HappyJet::parse(s).map(|jet| ExternalJet { index: jet.index() })
}
#[no_mangle]
pub fn display(jet: ExternalJet) -> String {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.to_string()
}

#[no_mangle]
pub fn source_jet_classification(jet: ExternalJet) -> SourceJetClassification {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.source_jet_classification()
}

#[no_mangle]
pub fn target_jet_classification(jet: ExternalJet) -> TargetJetClassification {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.target_jet_classification()
}

#[no_mangle]
pub fn is_disabled(jet: ExternalJet) -> bool {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.is_disabled()
}

#[no_mangle]
pub fn verify() -> ExternalJet {
    let jet = HappyJet::Verify;

    ExternalJet { index: jet.index() }
}

#[no_mangle]
pub fn conjure(jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
    jet.as_any()
        .downcast_ref::<HappyJet>()
        .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
}
