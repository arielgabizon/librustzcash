extern crate hex;
extern crate pirate;
extern crate zcash_client_backend;
extern crate zip32;

use std::env;
use zcash_client_backend::{
    address::encode_payment_address, constants::HRP_SAPLING_EXTENDED_SPENDING_KEY_TEST,
    welding_rig::scan_block, RpcChainSync,
};
use zip32::{ChildIndex, ExtendedFullViewingKey, ExtendedSpendingKey};

fn hex_reverse(data: &[u8]) -> String {
    let mut data = data.to_vec();
    data.reverse();
    hex::encode(data)
}

// Testnet blocks with transactions sent to the dummy account:
// - 343987
// - 343994
fn main() {
    let options = vec![
        "H/host#IP that zcashd is listening on; default=127.0.0.1",
        "p/port#Port that zcashd's JSON-RPC interface is on; default=18232",
        "s/start#Block height to synchronise from; default=343900",
        ":/user#Value of rpcuser in zcash.conf",
        ":/password#Value of rpcpassword in zcash.conf",
    ];

    let mut vars = match pirate::vars("rpcsync", &options) {
        Ok(v) => v,
        Err(why) => panic!("Error: {}", why),
    };

    let args: Vec<String> = env::args().collect();
    let matches = match pirate::matches(&args, &mut vars) {
        Ok(m) => m,
        Err(why) => {
            println!("Error: {}", why);
            pirate::usage(&vars);
            return;
        }
    };

    let host = match matches.get("host") {
        Some(host) => host,
        None => "127.0.0.1",
    };
    let port = match matches.get("port") {
        Some(p) => p.parse::<u32>().unwrap(),
        None => 18232,
    };
    let start = match matches.get("start") {
        Some(s) => s.parse::<u32>().unwrap(),
        None => 343900,
    };
    let user = matches.get("user").map(|s| s.clone());
    let password = matches.get("password").map(|s| s.clone());

    let server = format!("http://{}:{}", host, port);
    let cs = RpcChainSync::new(server, user, password);
    let mut session = match cs.start_session(start) {
        Ok((session, _)) => session,
        Err(e) => panic!("Failed to start session: {}", e),
    };

    // Generate the ExtendedFullViewingKey for the dummy account.
    let master = ExtendedSpendingKey::master(&b"dummyseed"[..]);
    let extsk = ExtendedSpendingKey::from_path(
        &master,
        &[
            ChildIndex::from_index(0x80000020), // ZIP 32
            ChildIndex::from_index(0x80000001), // Testnet
            ChildIndex::from_index(0x80000000), // Account 0
        ],
    );
    let extfvks = [ExtendedFullViewingKey::from(&extsk)];

    println!(
        "Dummy account address: {}",
        encode_payment_address(
            HRP_SAPLING_EXTENDED_SPENDING_KEY_TEST,
            &extsk.default_address().unwrap().1
        )
    );

    let mut total = 0;
    while let Some(block) = session.next() {
        let block = block.unwrap();
        let height = block.get_id().get_blockHeight();
        let hash = hex_reverse(block.get_id().get_blockHash());

        let txs = scan_block(block, &extfvks);
        if !txs.is_empty() {
            println!("Block {}: {}", height, hash)
        }

        for tx in txs {
            println!("  txid: {}", tx.txid);
            println!("    Shielded Spends: {}", tx.num_spends);
            println!("    Shielded Outputs: {}", tx.num_outputs);
            for output in tx.shielded_outputs {
                println!("    - index: {}", output.index);
                println!("      account: {}", output.account);
                println!("      value: {}", output.value);
                total += output.value;
            }
        }
    }
    println!("Total received: {}", total);
}
