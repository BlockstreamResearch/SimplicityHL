//! Isolated regtest lifecycle against the pinned Simplicity-enabled Bitcoin node.
use std::{error::Error, io::Write, path::Path};

use elementsd::bitcoincore_rpc::{
    jsonrpc::serde_json::{json, Value},
    RpcApi,
};
use elementsd::bitcoind::{self, tempfile::NamedTempFile, BitcoinD};
use simplicityhl::simplicity::bitcoin::{self, consensus, secp256k1, Amount, Block, Transaction};

#[path = "common/bitcoin.rs"]
mod bitcoin_program;

fn decode<T: consensus::Decodable>(value: &Value) -> Result<T, Box<dyn Error>> {
    Ok(consensus::encode::deserialize_hex(
        value.as_str().ok_or("expected transaction/block hex")?,
    )?)
}

#[test]
fn bitcoin_spend_utxo() -> Result<(), Box<dyn Error>> {
    let exe = std::env::var_os("BITCOIND_EXE")
        .ok_or("Set BITCOIND_EXE to the Simplicity-enabled v29.2-inq-simplicity bitcoind")?;
    let mut conf = bitcoind::Conf::default();
    conf.args.extend([
        "-connect=0",
        "-discover=0",
        "-dnsseed=0",
        "-vbparams=simplicity:0:9223372036854775807",
    ]);
    // BitcoinD owns a fresh temporary directory, disables P2P, and stops on drop.
    let daemon = BitcoinD::with_conf(exe, &conf)?;
    let wallet = daemon.create_wallet("bitcoin-roundtrip")?;
    let call = |method: &str, args: &[Value]| wallet.call::<Value>(method, args);
    assert_eq!(call("getblockchaininfo", &[])?["chain"], "regtest");
    assert_eq!(call("getconnectioncount", &[])?, 0);
    let address = call("getnewaddress", &[json!("return"), json!("bech32m")])?;
    assert_eq!(
        call("getaddressinfo", std::slice::from_ref(&address))?["ismine"],
        true
    );

    // Follow the pinned node's activation sequence, using its advertised signal.
    call("generatetoaddress", &[json!(144), address.clone()])?;
    let deployment = call("getdeploymentinfo", &[])?;
    let simplicity = &deployment["deployments"]["simplicity"];
    assert_eq!(simplicity["heretical"]["status"], "started");
    let signal = simplicity["heretical"]["signal_activate"]
        .as_str()
        .ok_or("compatible node must advertise the Simplicity activation signal")?;
    let version = u32::from_str_radix(signal.trim_start_matches("0x"), 16)?;
    let mined = call("generateblock", &[address.clone(), json!([]), json!(false)])?;
    let mut block: Block = decode(&mined["hex"])?;
    block.header.version = bitcoin::block::Version::from_consensus(version as i32);
    while block.header.validate_pow(block.header.target()).is_err() {
        block.header.nonce = block.header.nonce.checked_add(1).ok_or("nonce exhausted")?;
    }
    assert!(call(
        "submitblock",
        &[json!(consensus::encode::serialize_hex(&block))]
    )?
    .is_null());
    call("generatetoaddress", &[json!(288), address.clone()])?;
    assert_eq!(
        call("getdeploymentinfo", &[])?["deployments"]["simplicity"]["active"],
        true
    );

    // A new random script key and a new wallet belong only to this test run.
    let secret = secp256k1::SecretKey::new(&mut actual_rand::thread_rng());
    let mut key_file = NamedTempFile::new()?;
    writeln!(key_file, "{}", secret.display_secret())?;
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/bitcoin_p2pk.simf");
    let mut args = vec![
        "bitcoin_spend_utxo".to_owned(),
        "prepare".to_owned(),
        source.to_str().ok_or("non-UTF8 source path")?.to_owned(),
        key_file
            .path()
            .to_str()
            .ok_or("non-UTF8 temporary path")?
            .to_owned(),
        "regtest".to_owned(),
    ];
    let prepared = bitcoin_program::run(&args)?;
    let fund_txid = call(
        "sendtoaddress",
        &[prepared["address"].clone(), json!(0.001)],
    )?;
    call("generatetoaddress", &[json!(1), address.clone()])?;
    let funding = call("gettransaction", std::slice::from_ref(&fund_txid))?;
    assert!(funding["confirmations"].as_u64().unwrap_or(0) >= 1);
    let fund_tx: Transaction = decode(&funding["hex"])?;
    let lock_address = prepared["address"]
        .as_str()
        .ok_or("missing lock address")?
        .parse::<bitcoin::Address<_>>()?
        .require_network(bitcoin::Network::Regtest)?;
    let (index, output) = fund_tx
        .output
        .iter()
        .enumerate()
        .find(|(_, out)| out.script_pubkey == lock_address.script_pubkey())
        .ok_or("funding output missing")?;
    assert_eq!(output.value, Amount::from_sat(100_000));
    let return_address = address.as_str().ok_or("missing return address")?;
    let unsigned = call(
        "createrawtransaction",
        &[
            json!([{"txid": fund_txid, "vout": index}]),
            json!([{return_address: 0.00099}]),
        ],
    )?;
    let mut request = NamedTempFile::new()?;
    write!(
        request,
        "{}",
        json!({
            "unsigned_tx": unsigned,
            "utxo_value_sat": output.value.to_sat(),
            "utxo_script": output.script_pubkey.to_hex_string(),
        })
    )?;
    args[1] = "spend".to_owned();
    args[4] = request
        .path()
        .to_str()
        .ok_or("non-UTF8 temporary path")?
        .to_owned();
    let signed = bitcoin_program::run(&args)?;
    let spend: Transaction = decode(&signed["transaction"])?;
    let return_script = return_address
        .parse::<bitcoin::Address<_>>()?
        .require_network(bitcoin::Network::Regtest)?
        .script_pubkey();
    assert_eq!(spend.output.len(), 1);
    assert_eq!(spend.output[0].script_pubkey, return_script);
    assert_eq!(spend.output[0].value, Amount::from_sat(99_000));
    let acceptance = call("testmempoolaccept", &[json!([signed["transaction"]])])?;
    assert_eq!(acceptance[0]["allowed"], true, "{acceptance}");
    let spend_txid = call("sendrawtransaction", &[signed["transaction"].clone()])?;
    assert_eq!(spend_txid, signed["txid"]);
    call("generatetoaddress", &[json!(1), address])?;
    let confirmed = call("gettransaction", std::slice::from_ref(&spend_txid))?;
    assert!(confirmed["confirmations"].as_u64().unwrap_or(0) >= 1);
    println!("Confirmed Bitcoin lock {fund_txid} and same-wallet spend {spend_txid}");
    Ok(())
}
