use exonum_jsonrpc::client::Client;
use failure::Error;
use hex;
use hex_serde;
use serde::{
    de::{self, Deserialize, Deserializer, Unexpected, Visitor},
    ser::{Serialize, Serializer},
};
use std::fmt;

use welding_rig::block::{BlockID, CompactBlock, CompactOutput, CompactSpend, CompactTx};

#[derive(Debug)]
pub struct BitcoinUint256([u8; 32]);

impl Serialize for BitcoinUint256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut data = self.0.to_vec();
        data.reverse();
        serializer.serialize_str(&hex::encode(data))
    }
}

impl<'de> Deserialize<'de> for BitcoinUint256 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(BitcoinUint256Visitor)
    }
}

struct BitcoinUint256Visitor;

impl<'de> Visitor<'de> for BitcoinUint256Visitor {
    type Value = BitcoinUint256;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a 32-byte array")
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        if s.len() == 64 {
            match hex::decode(s) {
                Ok(mut data) => {
                    data.reverse();
                    let mut hash = [0u8; 32];
                    hash.copy_from_slice(&data);
                    Ok(BitcoinUint256(hash))
                }
                Err(e) => Err(de::Error::invalid_value(Unexpected::Str(s), &self)),
            }
        } else {
            Err(de::Error::invalid_value(Unexpected::Str(s), &self))
        }
    }
}

#[derive(Deserialize)]
struct GetBlockResult {
    hash: BitcoinUint256,
    height: u32,
    version: i32,
    merkleroot: BitcoinUint256,
    finalsaplingroot: BitcoinUint256,
    tx: Vec<BitcoinUint256>,
    time: u32,
    nonce: BitcoinUint256,
    #[serde(with = "hex_serde")]
    solution: Vec<u8>,
    #[serde(with = "hex_serde")]
    bits: [u8; 4],
    previousblockhash: BitcoinUint256,
    #[serde(default)]
    nextblockhash: Option<BitcoinUint256>,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
struct ShieldedSpendResult {
    nullifier: BitcoinUint256,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
struct ShieldedOutputResult {
    cmu: BitcoinUint256,
    ephemeralKey: BitcoinUint256,
    #[serde(with = "hex_serde")]
    encCiphertext: Vec<u8>,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
struct GetRawTransactionResult {
    txid: BitcoinUint256,
    vShieldedSpend: Vec<ShieldedSpendResult>,
    vShieldedOutput: Vec<ShieldedOutputResult>,
}

/// A light client chain synchronisation backend using the `zcashd` JSON-RPC interface.
pub struct RpcChainSync {
    server: String,
    user: Option<String>,
    password: Option<String>,
}

impl RpcChainSync {
    pub fn new<S: Into<String>>(server: S, user: Option<S>, password: Option<S>) -> Self {
        RpcChainSync {
            server: server.into(),
            user: user.map(|s| s.into()),
            password: password.map(|s| s.into()),
        }
    }

    pub fn start_session(
        &self,
        start_height: u32,
    ) -> Result<
        (
            Box<Iterator<Item = Result<CompactBlock, Error>>>,
            Option<u32>,
        ),
        Error,
    > {
        let client = Client::new(
            self.server.clone(),
            self.user.clone(),
            self.password.clone(),
        );

        // Find the first block hash we need to request
        let req = client.build_request("getblockhash".to_owned(), vec![json!(start_height)]);
        match client.send_request(&req) {
            Ok(ret) => match ret.into_result() {
                Ok(next_block_hash) => Ok((
                    Box::new(RpcChainSession {
                        client,
                        next_block_hash,
                    }),
                    None,
                )),
                Err(e) => Err(format_err!("zcashd returned error: {}", e)),
            },
            Err(e) => Err(format_err!("Error while fetching next block: {}", e)),
        }
    }
}

struct RpcChainSession {
    client: Client,
    next_block_hash: Option<BitcoinUint256>,
}

impl Iterator for RpcChainSession {
    type Item = Result<CompactBlock, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_block_hash = self.next_block_hash.take();

        // Fetch the next block
        let block = match next_block_hash {
            Some(hash) => {
                let req = self
                    .client
                    .build_request("getblock".to_owned(), vec![json!(hash)]);
                match self.client.send_request(&req) {
                    Ok(ret) => match ret.into_result::<GetBlockResult>() {
                        Ok(block) => block,
                        Err(e) => return Some(Err(format_err!("zcashd returned error: {}", e))),
                    },
                    Err(e) => {
                        return Some(Err(format_err!("Error while fetching next block: {}", e)))
                    }
                }
            }
            None => return None,
        };

        let mut txs = vec![];
        for (tx_index, txid) in block.tx.into_iter().enumerate() {
            // Fetch the transaction components
            let req = self
                .client
                .build_request("getrawtransaction".to_owned(), vec![json!(txid), json!(1)]);
            let tx = match self.client.send_request(&req) {
                Ok(ret) => match ret.into_result::<GetRawTransactionResult>() {
                    Ok(tx) => tx,
                    Err(e) => return Some(Err(format_err!("zcashd returned error: {}", e))),
                },
                Err(e) => return Some(Err(format_err!("Error while fetching transaction: {}", e))),
            };

            // Assemble the compact transaction
            let mut ctx = CompactTx::new();
            ctx.set_txIndex(tx_index as u64);
            ctx.set_txHash(tx.txid.0.to_vec());
            ctx.set_spends(
                tx.vShieldedSpend
                    .into_iter()
                    .map(|spend| {
                        let mut cspend = CompactSpend::new();
                        cspend.set_nf(spend.nullifier.0.to_vec());
                        cspend
                    }).collect(),
            );
            ctx.set_outputs(
                tx.vShieldedOutput
                    .into_iter()
                    .map(|output| {
                        let mut coutput = CompactOutput::new();
                        coutput.set_cmu(output.cmu.0.to_vec());
                        coutput.set_epk(output.ephemeralKey.0.to_vec());
                        coutput.set_ciphertext(output.encCiphertext[..52].to_vec());
                        coutput
                    }).collect(),
            );
            txs.push(ctx);
        }

        // Store the next block hash we need to request
        self.next_block_hash = block.nextblockhash;

        // Assemble and return the compact block
        let mut cb_id = BlockID::new();
        cb_id.set_blockHash(block.hash.0.to_vec());
        cb_id.set_blockHeight(block.height.into());
        let mut cb = CompactBlock::new();
        cb.set_id(cb_id);
        cb.set_vtx(txs.into_iter().collect());
        Some(Ok(cb))
    }
}
