#[macro_use]
extern crate failure;

extern crate bech32;
extern crate bellman;
extern crate blake2_rfc;
extern crate byteorder;
extern crate chacha20_poly1305_aead;
extern crate hex;
extern crate pairing;
extern crate protobuf;
extern crate rand;
extern crate sapling_crypto;
extern crate zcash_primitives;
extern crate zcash_proofs;
extern crate zip32;

#[cfg(feature = "jsonrpc")]
extern crate exonum_jsonrpc;

#[cfg(feature = "jsonrpc")]
extern crate hex_serde;

#[cfg(feature = "jsonrpc")]
extern crate serde;

#[cfg(feature = "jsonrpc")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "jsonrpc")]
#[macro_use]
extern crate serde_json;

pub mod address;
pub mod constants;
pub mod data;
pub mod keystore;
mod note_encryption;
pub mod prover;
pub mod wallet;
pub mod welding_rig;

#[cfg(feature = "jsonrpc")]
mod jsonrpc;

#[cfg(feature = "jsonrpc")]
pub use jsonrpc::RpcChainSync;
