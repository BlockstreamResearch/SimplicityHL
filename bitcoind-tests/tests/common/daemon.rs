use std::str::FromStr;

use elements::encode::{deserialize, serialize_hex};
use elements::hex::FromHex;
use elementsd::bitcoincore_rpc::jsonrpc::serde_json::Value;
use elementsd::bitcoind::bitcoincore_rpc::RpcApi;
use elementsd::ElementsD;
use simplicityhl::elements;

// We are not using pegins right now, but it might be required in case in future
// if we extend the tests to check pegins etc.
pub fn setup() -> (ElementsD, elements::BlockHash) {
    let mut conf = elementsd::Conf::new(None);

    // HACK: Upstream has issued only 21 million sats intially, but our hard coded tests
    // consume more coins. In order to avoid further conflicts, mutate the default arg here.

    let arg_pos = conf
        .0
        .args
        .iter()
        .position(|x| x.starts_with("-initialfreecoins="));

    match arg_pos {
        Some(i) => conf.0.args[i] = "-initialfreecoins=210000000000",
        None => conf.0.args.push("-initialfreecoins=210000000000"),
    };
    conf.0.args.push("-evbparams=simplicity:-1:::");

    let elementsd = ElementsD::with_conf(elementsd::exe_path().unwrap(), &conf).unwrap();

    let create = elementsd.call("createwallet", &["wallet".into()]);
    assert_eq!(create.get("name").unwrap(), "wallet");

    let rescan = elementsd.call("rescanblockchain", &[]);
    assert_eq!(rescan.get("stop_height").unwrap().as_u64().unwrap(), 0);

    let balances = elementsd.call("getbalances", &[]);
    let mine = balances.get("mine").unwrap();
    let trusted = mine.get("trusted").unwrap();
    assert_eq!(trusted.get("bitcoin").unwrap(), 2100.0);

    let genesis_str = elementsd.call("getblockhash", &[0u32.into()]);
    let genesis_str = genesis_str.as_str().unwrap();
    let genesis_hash = elements::BlockHash::from_str(genesis_str).unwrap();

    (elementsd, genesis_hash)
}
// Upstream all common methods later
pub trait Call {
    fn call(&self, cmd: &str, args: &[Value]) -> Value;
    fn get_new_address(&self) -> elements::Address;
    fn send_to_address(&self, addr: &elements::Address, amt: &str) -> elements::Txid;
    fn get_transaction(&self, txid: &elements::Txid) -> elements::Transaction;
    fn send_raw_transaction(&self, hex: &elements::Transaction) -> elements::Txid;
    fn generate(&self, blocks: u32);
}

impl Call for ElementsD {
    fn call(&self, cmd: &str, args: &[Value]) -> Value {
        self.client().call::<Value>(cmd, args).unwrap()
    }

    fn get_new_address(&self) -> elements::Address {
        let addr_str = self
            .call("getnewaddress", &[])
            .as_str()
            .unwrap()
            .to_string();

        elements::Address::from_str(&addr_str).unwrap()
    }

    fn get_transaction(&self, txid: &elements::Txid) -> elements::Transaction {
        let tx_hex = self.call("gettransaction", &[txid.to_string().into()])["hex"]
            .as_str()
            .unwrap()
            .to_string();

        let tx_bytes = Vec::<u8>::from_hex(&tx_hex).unwrap();
        deserialize(&tx_bytes).unwrap()
    }

    fn send_to_address(&self, addr: &elements::Address, amt: &str) -> elements::Txid {
        let tx_id = self
            .call("sendtoaddress", &[addr.to_string().into(), amt.into()])
            .as_str()
            .unwrap()
            .to_string();
        elements::Txid::from_str(&tx_id).unwrap()
    }

    fn send_raw_transaction(&self, tx: &elements::Transaction) -> elements::Txid {
        let tx_id = self
            .call("sendrawtransaction", &[serialize_hex(tx).into()])
            .as_str()
            .unwrap()
            .to_string();

        elements::Txid::from_str(&tx_id).unwrap()
    }

    fn generate(&self, blocks: u32) {
        let address = self.get_new_address();
        let _value = self.call(
            "generatetoaddress",
            &[blocks.into(), address.to_string().into()],
        );
    }
}
