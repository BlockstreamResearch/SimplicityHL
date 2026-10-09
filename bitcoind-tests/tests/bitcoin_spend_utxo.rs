//! Pinned node: Bitcoin Inquisition `v29.2-inq-simplicity`
//! (https://github.com/delta1/bitcoin/releases/tag/v29.2-inq-simplicity).

use std::collections::HashMap;
use std::str::FromStr;

use elementsd::bitcoincore_rpc::jsonrpc::serde_json::{json, Value};
use elementsd::bitcoincore_rpc::{Client, RpcApi};
use elementsd::bitcoind::{self, BitcoinD};
use simplicityhl::ast::ElementsJetHinter;
use simplicityhl::num::U256;
use simplicityhl::simplicity::bitcoin::{
    absolute, block, consensus, secp256k1, taproot, transaction, Address, Amount, Block, Network,
    OutPoint, ScriptBuf, Transaction, TxIn, TxOut, Witness,
};
use simplicityhl::simplicity::jet::BitcoinEnv;
use simplicityhl::value::ValueConstructible;
use simplicityhl::{
    Arguments, CompiledProgram, TemplateProgramWitness, UnstableFeature, UnstableFeatures,
    Value as SimValue, WitnessNameToValueMap, WitnessValues,
};

/// The tapleaf version of Simplicity programs on the pinned node.
const SIMPLICITY_LEAF_VERSION: u8 = 0xbe;
const UNSPENDABLE_INTERNAL_KEY: &str =
    "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0";

const LOCKED: Amount = Amount::from_sat(100_000);
const RETURNED: Amount = Amount::from_sat(99_000);

fn simplicity_deployment(rpc: &Client) -> Value {
    rpc.call::<Value>("getdeploymentinfo", &[]).unwrap()["deployments"]["simplicity"].clone()
}

/// Activate the node's Simplicity deployment: after the first period it accepts
/// one block signalling activation, and it is active two periods later.
fn activate_simplicity(rpc: &Client, address: &Address) {
    rpc.generate_to_address(144, address).unwrap();
    let deployment = simplicity_deployment(rpc);
    assert_eq!(deployment["heretical"]["status"], "started");

    let signal = deployment["heretical"]["signal_activate"].as_str().unwrap();
    let version = i32::from_str_radix(signal.trim_start_matches("0x"), 16).unwrap();

    let template: Value = rpc
        .call(
            "generateblock",
            &[json!(address.to_string()), json!([]), json!(false)],
        )
        .unwrap();
    let mut block: Block =
        consensus::encode::deserialize_hex(template["hex"].as_str().unwrap()).unwrap();

    block.header.version = block::Version::from_consensus(version);
    while block.header.validate_pow(block.header.target()).is_err() {
        block.header.nonce += 1;
    }
    rpc.submit_block(&block).unwrap();

    rpc.generate_to_address(288, address).unwrap();
    assert_eq!(simplicity_deployment(rpc)["active"], true);
}

struct P2pk {
    key: secp256k1::Keypair,
    program: CompiledProgram,
    script: ScriptBuf,
    control_block: taproot::ControlBlock,
    address: Address,
}

impl P2pk {
    fn new() -> Self {
        let secp = secp256k1::Secp256k1::new();
        let key = secp256k1::Keypair::from_seckey_slice(&secp, &[1; 32]).unwrap();
        let arguments = Arguments::from_map(HashMap::from([(
            TemplateProgramWitness::parameter_from_str("ALICE_PUBLIC_KEY"),
            SimValue::u256(U256::from_byte_array(key.x_only_public_key().0.serialize())),
        )]));
        let program = CompiledProgram::new_with_unstable(
            include_str!("../../examples/bitcoin_p2pk.simf"),
            &UnstableFeatures::new([UnstableFeature::Bitcoin]),
            arguments,
            false,
            Box::new(ElementsJetHinter::new()),
        )
        .unwrap();

        // The tapleaf script is the program's CMR.
        let script = ScriptBuf::from_bytes(program.commit().cmr().as_ref().to_vec());
        let leaf_version = taproot::LeafVersion::from_consensus(SIMPLICITY_LEAF_VERSION).unwrap();
        let internal_key = secp256k1::XOnlyPublicKey::from_str(UNSPENDABLE_INTERNAL_KEY).unwrap();
        let info = taproot::TaprootBuilder::new()
            .add_leaf_with_ver(0, script.clone(), leaf_version)
            .unwrap()
            .finalize(&secp, internal_key)
            .unwrap();
        let control_block = info.control_block(&(script.clone(), leaf_version)).unwrap();
        let address = Address::p2tr_tweaked(info.output_key(), Network::Regtest);

        Self {
            key,
            program,
            script,
            control_block,
            address,
        }
    }

    fn spend(&self, previous_output: OutPoint, utxo: TxOut, to: &Address) -> Transaction {
        let mut tx = Transaction {
            version: transaction::Version::TWO,
            lock_time: absolute::LockTime::ZERO,
            input: vec![TxIn {
                previous_output,
                ..Default::default()
            }],
            output: vec![TxOut {
                value: RETURNED,
                script_pubkey: to.script_pubkey(),
            }],
        };

        let env = BitcoinEnv::new(
            tx.clone(),
            &[utxo],
            0,
            self.program.commit().cmr(),
            self.control_block.clone(),
        );
        let sighash = env.c_tx_env().sighash_all().to_byte_array();
        let signature = secp256k1::Secp256k1::new()
            .sign_schnorr_no_aux_rand(&secp256k1::Message::from_digest(sighash), &self.key);
        let witness = WitnessValues::from_map(HashMap::from([(
            TemplateProgramWitness::witness_from_str("ALICE_SIGNATURE"),
            SimValue::byte_array(signature.serialize()),
        )]));
        let satisfied = self
            .program
            .satisfy_with_bitcoin_env(witness, &env)
            .unwrap();

        let (program_bytes, witness_bytes) = satisfied.redeem().to_vec_with_witness();
        let mut stack = vec![
            witness_bytes,
            program_bytes,
            self.script.to_bytes(),
            self.control_block.serialize(),
        ];

        // Bitcoin has no annex, so the budget padding is an all-zero stack item.
        // `Cost::get_padding_bytes` would build the Elements annex form here.
        if let Some(len) = satisfied.redeem().bounds().cost.get_padding_size(&stack) {
            stack.insert(0, vec![0; len]);
        }
        tx.input[0].witness = Witness::from_slice(&stack);
        tx
    }
}

#[test]
fn bitcoin_spend_utxo() {
    let mut conf = bitcoind::Conf::default();
    conf.args.push("-vbparams=simplicity:0:9223372036854775807");
    let exe = bitcoind::exe_path().expect("set BITCOIND_EXE to a Simplicity-enabled bitcoind");
    let daemon = BitcoinD::with_conf(exe, &conf).unwrap();
    let rpc = daemon.create_wallet("wallet").unwrap();
    let wallet = rpc
        .get_new_address(None, None)
        .unwrap()
        .require_network(Network::Regtest)
        .unwrap();

    activate_simplicity(&rpc, &wallet);

    let p2pk = P2pk::new();
    let fund_txid = rpc
        .send_to_address(&p2pk.address, LOCKED, None, None, None, None, None, None)
        .unwrap();
    rpc.generate_to_address(1, &wallet).unwrap();

    let funding = rpc
        .get_transaction(&fund_txid, None)
        .unwrap()
        .transaction()
        .unwrap();
    let vout = funding
        .output
        .iter()
        .position(|out| out.script_pubkey == p2pk.address.script_pubkey())
        .unwrap();

    let spend = p2pk.spend(
        OutPoint::new(fund_txid, vout as u32),
        funding.output[vout].clone(),
        &wallet,
    );
    // The node runs the Simplicity program; a rejection reports its reason.
    let spend_txid = rpc.send_raw_transaction(&spend).unwrap();
    rpc.generate_to_address(1, &wallet).unwrap();

    let confirmations = rpc
        .get_transaction(&spend_txid, None)
        .unwrap()
        .info
        .confirmations;
    assert_eq!(confirmations, 1);
}
