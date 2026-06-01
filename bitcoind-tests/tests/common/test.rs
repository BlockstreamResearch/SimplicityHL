use std::str::FromStr;

use elements::hashes::Hash;
use elements::pset::PartiallySignedTransaction as Psbt;
use elements::{confidential, secp256k1_zkp as secp256k1};
use elementsd::ElementsD;
use secp256k1::XOnlyPublicKey;
use simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicityhl::ast::ElementsJetHinter;
use simplicityhl::{elements, simplicity};

use crate::common::daemon::Call;

type FnWitness = fn([u8; 32]) -> simplicityhl::WitnessValues;

pub struct TestCase<'a> {
    pub name: &'static str,
    template: Option<simplicityhl::TemplateProgram>,
    compiled: Option<simplicityhl::CompiledProgram>,
    witness: FnWitness,
    lock_time: elements::LockTime,
    sequence: elements::Sequence,
    daemon: &'a ElementsD,
    genesis_hash: elements::BlockHash,
    funding: Option<Funding>,
}

#[derive(Clone)]
struct Funding {
    address: elements::Address,
    txid: elements::Txid,
}

impl<'a> TestCase<'a> {
    pub fn new(daemon: &'a ElementsD, genesis_hash: elements::BlockHash) -> Self {
        Self {
            name: "test name is missing",
            template: None,
            compiled: None,
            witness: empty_witness,
            lock_time: elements::LockTime::ZERO,
            sequence: elements::Sequence::ZERO,
            daemon,
            genesis_hash,
            funding: None,
        }
    }

    pub fn name(mut self, name: &'static str) -> Self {
        self.name = name;
        self
    }

    pub fn program_path<P: AsRef<std::path::Path>>(mut self, path: P) -> Self {
        let text = std::fs::read_to_string(path).expect("path should be readable");
        let compiled = simplicityhl::CompiledProgram::new(
            text.as_str(),
            simplicityhl::Arguments::default(),
            false,
            Box::new(ElementsJetHinter::new()),
        )
        .expect("program should compile");
        self.compiled = Some(compiled);
        self
    }

    pub fn template_path<P: AsRef<std::path::Path>>(mut self, path: P) -> Self {
        let text = std::fs::read_to_string(path).expect("path should be readable");
        let template =
            simplicityhl::TemplateProgram::new(text.as_str(), Box::new(ElementsJetHinter::new()))
                .expect("program should compile");
        self.template = Some(template);
        self
    }

    pub fn arguments(mut self, arguments: simplicityhl::Arguments) -> Self {
        let compiled = self
            .template
            .as_ref()
            .expect("template should exist")
            .instantiate(arguments, false)
            .expect("arguments should be consistent with the program");
        self.compiled = Some(compiled);
        self
    }

    pub fn witness(mut self, witness: FnWitness) -> Self {
        self.witness = witness;
        self
    }

    pub fn lock_time(mut self, lock_time: elements::LockTime) -> Self {
        self.lock_time = lock_time;
        self
    }

    pub fn sequence(mut self, sequence: elements::Sequence) -> Self {
        self.sequence = sequence;
        self
    }

    fn script_ver(&self) -> (elements::Script, elements::taproot::LeafVersion) {
        let script = elements::script::Script::from(
            self.compiled
                .as_ref()
                .expect("program should be defined")
                .commit()
                .cmr()
                .as_ref()
                .to_vec(),
        );
        (script, simplicity::leaf_version())
    }

    fn taproot_spend_info(&self) -> elements::taproot::TaprootSpendInfo {
        let internal_key = XOnlyPublicKey::from_str(
            "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0",
        )
        .unwrap();
        let builder = elements::taproot::TaprootBuilder::new();
        let (script, version) = self.script_ver();
        let builder = builder
            .add_leaf_with_ver(0, script, version)
            .expect("tap tree should be valid");
        builder
            .finalize(secp256k1::SECP256K1, internal_key)
            .expect("tap tree should be valid")
    }

    // Find the Outpoint by value.
    // Ideally, we should find by scriptPubkey, but this
    // works for temp test case
    fn get_vout(&self) -> (elements::OutPoint, elements::TxOut) {
        let funding = self.funding.as_ref().expect("test funding is missing");
        let tx = self.daemon.get_transaction(&funding.txid);
        let script = funding.address.script_pubkey();
        for (vout, txout) in tx.output.into_iter().enumerate() {
            if txout.value == confidential::Value::Explicit(100_000_000)
                && txout.script_pubkey == script
            {
                return (elements::OutPoint::new(funding.txid, vout as u32), txout);
            }
        }
        unreachable!("Only call get vout on functions which have the expected outpoint");
    }

    pub fn create_utxo(&mut self) {
        let info = self.taproot_spend_info();
        let blinder = None;
        let address = elements::Address::p2tr(
            secp256k1::SECP256K1,
            info.internal_key(),
            info.merkle_root(),
            blinder,
            &elements::AddressParams::ELEMENTS,
        );
        let amount = "1";
        let txid = self.daemon.send_to_address(&address, amount);
        self.funding = Some(Funding { address, txid });
    }

    pub fn spend_utxo(&self) {
        let compiled = self.compiled.as_ref().expect("test program is missing");
        let (outpoint, utxo) = self.get_vout();
        let mut psbt = Psbt::from_tx(elements::Transaction {
            version: 2,
            lock_time: self.lock_time,
            input: vec![elements::TxIn {
                previous_output: outpoint,
                is_pegin: false,
                script_sig: elements::Script::new(),
                sequence: self.sequence,
                asset_issuance: elements::AssetIssuance::null(),
                witness: elements::TxInWitness::empty(),
            }],
            output: vec![
                elements::TxOut {
                    value: confidential::Value::Explicit(99_997_000),
                    script_pubkey: self.daemon.get_new_address().script_pubkey(),
                    asset: utxo.asset,
                    nonce: confidential::Nonce::Null,
                    witness: elements::TxOutWitness::empty(),
                },
                elements::TxOut::new_fee(3_000, utxo.asset.explicit().unwrap()),
            ],
        });
        let info = self.taproot_spend_info();
        let script_ver = self.script_ver();
        let control_block = info
            .control_block(&script_ver)
            .expect("control block should exist");
        let sighash_all = {
            let tx = psbt
                .extract_tx()
                .expect("transaction should be extractable");
            let utxos = vec![ElementsUtxo::from(utxo)];
            let index = 0;
            let annex = None;
            let env = ElementsEnv::new(
                &tx,
                utxos,
                index,
                compiled.commit().cmr(),
                control_block.clone(),
                annex,
                self.genesis_hash,
            );
            env.c_tx_env().sighash_all()
        };
        let witness_values = (self.witness)(sighash_all.to_byte_array());
        let satisfied_program = compiled
            .satisfy(witness_values)
            .expect("program should be satisfiable");
        let (program_bytes, witness_bytes) = satisfied_program.redeem().to_vec_with_witness();
        psbt.inputs_mut()[0].final_script_witness = Some(vec![
            witness_bytes,
            program_bytes,
            script_ver.0.into_bytes(),
            control_block.serialize(),
        ]);
        let tx = psbt
            .extract_tx()
            .expect("transaction should be extractable");

        let _txid = self.daemon.send_raw_transaction(&tx);
    }
}

fn empty_witness(_sighash_all: [u8; 32]) -> simplicityhl::WitnessValues {
    simplicityhl::WitnessValues::default()
}
