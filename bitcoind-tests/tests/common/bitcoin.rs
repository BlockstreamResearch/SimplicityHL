//! Offline helper for the isolated Bitcoin experiment. Never connects to a node.
//! Reads the test signing key from a private file; never prints it.
use std::{collections::HashMap, error::Error, fs, str::FromStr, sync::Arc};

use bitcoin::{
    consensus, secp256k1, taproot, Address, Amount, Network, ScriptBuf, Transaction, TxOut, Witness,
};
use elementsd::bitcoincore_rpc::jsonrpc::serde_json::{self, json, Value as Json};
use simplicityhl::simplicity::{self, bitcoin};
use simplicityhl::value::ValueConstructible;
use simplicityhl::{
    Arguments, CompiledProgram, TemplateProgramWitness, UnstableFeature, UnstableFeatures, Value,
    WitnessNameToValueMap, WitnessValues,
};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn unhex(s: &str) -> Result<Vec<u8>, Box<dyn Error>> {
    if !s.as_bytes().chunks_exact(2).remainder().is_empty() {
        return Err("hex length must be even".into());
    }
    s.as_bytes()
        .chunks_exact(2)
        .map(|pair| Ok(u8::from_str_radix(std::str::from_utf8(pair)?, 16)?))
        .collect()
}

pub fn run(args: &[String]) -> Result<Json, Box<dyn Error>> {
    if args.len() != 5 {
        return Err("expected helper arguments: name, mode, source, key file, and network or request JSON".into());
    }
    let source = fs::read_to_string(&args[2])?;
    let secret = secp256k1::SecretKey::from_str(fs::read_to_string(&args[3])?.trim())?;
    let secp = secp256k1::Secp256k1::new();
    let keypair = secp256k1::Keypair::from_secret_key(&secp, &secret);
    let public_key = keypair.x_only_public_key().0.serialize();
    let program = CompiledProgram::new_with_unstable(
        source,
        &UnstableFeatures::new([UnstableFeature::Bitcoin]),
        Arguments::from_map(HashMap::from([(
            TemplateProgramWitness::parameter_from_str("ALICE_PUBLIC_KEY"),
            Value::u256(simplicityhl::num::U256::from_byte_array(public_key)),
        )])),
        false,
        Box::new(simplicityhl::ast::SourceJetHinter::new()),
    )?;
    if program.compilation_target() != Some(simplicityhl::parse::CompilationTarget::Bitcoin) {
        return Err("source must declare target bitcoin".into());
    }
    let cmr = program.commit().cmr();
    let script = ScriptBuf::from_bytes(cmr.as_ref().to_vec());
    let leaf = taproot::LeafVersion::from_consensus(0xbe)?;
    let internal = secp256k1::XOnlyPublicKey::from_str(
        "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0",
    )?;
    let info = taproot::TaprootBuilder::new()
        .add_leaf_with_ver(0, script.clone(), leaf)?
        .finalize(&secp, internal)
        .map_err(|_| "invalid taproot tree")?;
    let control = info
        .control_block(&(script.clone(), leaf))
        .ok_or("missing control block")?;
    if args[1] == "prepare" {
        let network = match args[4].as_str() {
            "regtest" => Network::Regtest,
            "signet" => Network::Signet,
            _ => return Err("only regtest or signet allowed".into()),
        };
        Ok(
            json!({"target":"bitcoin","compiler_version":program.compiler_version(),"address":Address::p2tr_tweaked(info.output_key(),network).to_string(),"cmr":cmr.to_string(),"control_block":hex(&control.serialize()),"public_key":hex(&public_key)}),
        )
    } else if args[1] == "spend" {
        let request: Json = serde_json::from_str(&fs::read_to_string(&args[4])?)?;
        let mut tx: Transaction = consensus::deserialize(&unhex(
            request["unsigned_tx"]
                .as_str()
                .ok_or("unsigned_tx missing")?,
        )?)?;
        if tx.input.len() != 1 || tx.output.len() != 1 {
            return Err("experiment requires one input and one return output".into());
        }
        let utxo = TxOut {
            value: Amount::from_sat(
                request["utxo_value_sat"]
                    .as_u64()
                    .ok_or("utxo_value_sat missing")?,
            ),
            script_pubkey: ScriptBuf::from_bytes(unhex(
                request["utxo_script"]
                    .as_str()
                    .ok_or("utxo_script missing")?,
            )?),
        };
        if utxo.script_pubkey
            != Address::p2tr_tweaked(info.output_key(), Network::Regtest).script_pubkey()
        {
            return Err("funding script does not match compiled program".into());
        }
        if tx.output[0].value >= utxo.value {
            return Err("return amount must leave a positive fee".into());
        }
        let env = simplicity::jet::bitcoin::BitcoinEnv::new(
            Arc::new(tx.clone()),
            &[utxo],
            0,
            cmr,
            control.clone(),
        );
        let digest = env.c_tx_env().sighash_all().to_byte_array();
        let sig = secp.sign_schnorr_no_aux_rand(&secp256k1::Message::from_digest(digest), &keypair);
        let witnesses = WitnessValues::from_map(HashMap::from([(
            TemplateProgramWitness::witness_from_str("ALICE_SIGNATURE"),
            Value::byte_array(sig.serialize()),
        )]));
        let satisfied = program.satisfy_with_bitcoin_env(witnesses, &env)?;
        let (program_bytes, witness_bytes) = satisfied.redeem().to_vec_with_witness();
        let mut stack = vec![
            witness_bytes,
            program_bytes,
            script.into_bytes(),
            control.serialize(),
        ];
        let padding = satisfied.redeem().bounds().cost.get_padding_size(&stack);
        if let Some(size) = padding {
            stack.insert(0, vec![0; size]);
        }
        tx.input[0].witness = Witness::from_slice(&stack);
        let cost_milliweight: u64 = satisfied.redeem().bounds().cost.to_string().parse()?;
        let budget_milliweight =
            (consensus::serialize(&tx.input[0].witness).len() as u64 + 50) * 1000;
        if cost_milliweight > budget_milliweight {
            return Err("witness budget is insufficient after padding".into());
        }
        Ok(
            json!({"target":"bitcoin","compiler_version":program.compiler_version(),"transaction":consensus::encode::serialize_hex(&tx),"txid":tx.compute_txid().to_string(),"cmr":cmr.to_string(),"padding_bytes":padding,"cost_milliweight":cost_milliweight,"budget_milliweight":budget_milliweight,"sighash":hex(&digest)}),
        )
    } else {
        Err("unknown mode".into())
    }
}
