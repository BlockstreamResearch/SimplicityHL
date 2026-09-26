//! Dummy Elements environment for testing

use std::sync::Arc;

use elements::{confidential, taproot::ControlBlock, AssetIssuance};
use simplicity::elements;
use simplicity::elements::{AssetId, TxOut};
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicity::Cmr;

/// Return a dummy Elements environment.
pub fn dummy() -> ElementsEnv<Arc<elements::Transaction>> {
    dummy_with(elements::LockTime::ZERO, elements::Sequence::MAX, false)
}

/// Returns a default transaction for the Elements network.
fn create_default_transaction(
    lock_time: elements::LockTime,
    sequence: elements::Sequence,
    include_fee_output: bool,
) -> elements::Transaction {
    let mut tx = elements::Transaction {
        version: 2,
        lock_time,
        input: vec![elements::TxIn {
            previous_output: elements::OutPoint::default(),
            is_pegin: false,
            script_sig: elements::Script::new(),
            sequence,
            asset_issuance: AssetIssuance::default(),
            witness: elements::TxInWitness::default(),
        }],
        output: vec![elements::TxOut {
            asset: confidential::Asset::default(),
            value: confidential::Value::default(),
            nonce: confidential::Nonce::default(),
            script_pubkey: elements::Script::default(),
            witness: elements::TxOutWitness::default(),
        }],
    };

    if include_fee_output {
        tx.output.push(TxOut::new_fee(1_000, AssetId::default()));
    }
    tx
}

/// Returns a dummy Elements environment with a provided transaction.
pub fn dummy_with_tx(tx: elements::Transaction) -> ElementsEnv<Arc<elements::Transaction>> {
    let ctrl_blk: [u8; 33] = [
        0xc0, 0xeb, 0x04, 0xb6, 0x8e, 0x9a, 0x26, 0xd1, 0x16, 0x04, 0x6c, 0x76, 0xe8, 0xff, 0x47,
        0x33, 0x2f, 0xb7, 0x1d, 0xda, 0x90, 0xff, 0x4b, 0xef, 0x53, 0x70, 0xf2, 0x52, 0x26, 0xd3,
        0xbc, 0x09, 0xfc,
    ];
    let num_inputs = tx.input.len();

    ElementsEnv::new(
        Arc::new(tx),
        vec![
            ElementsUtxo {
                script_pubkey: elements::Script::default(),
                asset: confidential::Asset::default(),
                value: confidential::Value::default(),
            };
            num_inputs
        ],
        0,
        Cmr::from_byte_array([0; 32]),
        ControlBlock::from_slice(&ctrl_blk).unwrap(),
        None,
        elements::BlockHash::from_byte_array([0; 32]),
    )
}

/// Returns a dummy Elements environment with the given locktime and sequence.
pub fn dummy_with(
    lock_time: elements::LockTime,
    sequence: elements::Sequence,
    include_fee_output: bool,
) -> ElementsEnv<Arc<elements::Transaction>> {
    let default_tx = create_default_transaction(lock_time, sequence, include_fee_output);
    dummy_with_tx(default_tx)
}
