use pairing::bls12_381::{Bls12, Fr};
use sapling_crypto::jubjub::{edwards, PrimeOrder};
use zcash_primitives::transaction::TxId;

use data::EncCiphertextFrag;

pub struct WalletTx {
    pub txid: TxId,
    pub num_spends: usize,
    pub num_outputs: usize,
    pub shielded_outputs: Vec<WalletShieldedOutput>,
}

pub struct WalletShieldedOutput {
    pub index: usize,
    pub cmu: Fr,
    pub epk: edwards::Point<Bls12, PrimeOrder>,
    pub enc_ct: EncCiphertextFrag,
    pub account: usize,
    pub value: u64,
}
