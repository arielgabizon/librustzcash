extern crate hex;
extern crate pirate;
extern crate protobuf;
extern crate zcash_client_backend;

use protobuf::Message;
use std::env;
use zcash_client_backend::RpcChainSync;

fn hex_reverse(data: &[u8]) -> String {
    let mut data = data.to_vec();
    data.reverse();
    hex::encode(data)
}

// Testnet blocks with Sapling data:
// - 282635
// - 289461
// - 290807
// - 294035
fn main() {
    let options = vec![
        "H/host#IP that zcashd is listening on; default=127.0.0.1",
        "p/port#Port that zcashd's JSON-RPC interface is on; default=18232",
        "s/start#Block height to synchronise from; default=289460",
        "e/end#Block height to synchronise to; default=289465",
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
        None => 289460,
    };
    let end = match matches.get("end") {
        Some(e) => e.parse::<u64>().unwrap(),
        None => 289465,
    };
    let user = matches.get("user").map(|s| s.clone());
    let password = matches.get("password").map(|s| s.clone());

    let server = format!("http://{}:{}", host, port);
    let cs = RpcChainSync::new(server, user, password);
    let mut session = match cs.start_session(start) {
        Ok((session, _)) => session,
        Err(e) => panic!("Failed to start session: {}", e),
    };

    while let Some(block) = session.next() {
        let block = block.unwrap();
        println!(
            "Block {}: {}",
            block.get_id().get_blockHeight(),
            hex_reverse(block.get_id().get_blockHash())
        );
        println!(
            "  Compact: {}",
            hex::encode(block.write_to_bytes().unwrap())
        );
        for tx in block.get_vtx() {
            println!("  txid: {}", hex_reverse(tx.get_txHash()));
            if !tx.get_spends().is_empty() {
                println!("    Shielded Spends:");
                for spend in tx.get_spends() {
                    println!("    - nf: {}", hex_reverse(spend.get_nf()))
                }
            }
            if !tx.get_outputs().is_empty() {
                println!("    Shielded Outputs:");
                for output in tx.get_outputs() {
                    println!("    - cmu: {}", hex_reverse(output.get_cmu()));
                    println!("      epk: {}", hex_reverse(output.get_epk()));
                    println!("      enc_ct:");
                    println!("        {}...", hex::encode(output.get_ciphertext()));
                }
            }
        }

        if block.get_id().get_blockHeight() >= end {
            break;
        }
    }
}
