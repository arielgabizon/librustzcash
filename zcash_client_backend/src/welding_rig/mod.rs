use pairing::{
    bls12_381::{Bls12, Fr, FrRepr},
    PrimeField, PrimeFieldRepr,
};
use protobuf::parse_from_bytes;
use sapling_crypto::jubjub::{edwards, fs::Fs, PrimeOrder};
use zcash_primitives::{transaction::TxId, JUBJUB};
use zip32::ExtendedFullViewingKey;

use data::EncCiphertextFrag;
use note_encryption::try_sapling_compact_note_decryption;
use wallet::{WalletShieldedOutput, WalletTx};

pub mod block;

fn trial_decrypt(
    cmu: &Fr,
    epk: &edwards::Point<Bls12, PrimeOrder>,
    enc_ct: &[u8],
    ivk: &Fs,
) -> Option<u64> {
    match try_sapling_compact_note_decryption(ivk, epk, cmu, enc_ct) {
        Ok((note, to)) => Some(note.value),
        Err(_) => None,
    }
}

/// Returns a WalletShieldedOutput if this output belongs to any of the given
/// ExtendedFullViewingKeys.
fn scan_output(
    (index, output): (usize, block::CompactOutput),
    ivks: &[Fs],
) -> Option<WalletShieldedOutput> {
    let mut repr = FrRepr::default();
    if repr.read_le(&output.cmu[..]).is_err() {
        return None;
    }
    let cmu = match Fr::from_repr(repr) {
        Ok(cmu) => cmu,
        Err(_) => return None,
    };

    let epk = match edwards::Point::<Bls12, _>::read(&output.epk[..], &JUBJUB) {
        Ok(p) => match p.as_prime_order(&JUBJUB) {
            Some(epk) => epk,
            None => return None,
        },
        Err(_) => return None,
    };

    let ct = output.ciphertext;

    for (account, ivk) in ivks.iter().enumerate() {
        let value = match trial_decrypt(&cmu, &epk, &ct, ivk) {
            Some(value) => value,
            None => continue,
        };

        // It's ours, so let's copy the ciphertext fragment and return
        let mut enc_ct = EncCiphertextFrag([0u8; 52]);
        enc_ct.0.copy_from_slice(&ct);

        return Some(WalletShieldedOutput {
            index,
            cmu,
            epk,
            enc_ct,
            account,
            value,
        });
    }
    None
}

/// Returns a WalletTx if this transaction belongs to any of the given
/// ExtendedFullViewingKeys.
fn scan_tx(tx: block::CompactTx, extfvks: &[ExtendedFullViewingKey]) -> Option<WalletTx> {
    let num_spends = tx.spends.len();
    let num_outputs = tx.outputs.len();

    // Check for incoming notes
    let shielded_outputs: Vec<WalletShieldedOutput> = {
        let ivks: Vec<_> = extfvks.iter().map(|extfvk| extfvk.fvk.vk.ivk()).collect();
        tx.outputs
            .into_iter()
            .enumerate()
            .filter_map(|(index, output)| scan_output((index, output), &ivks))
            .collect()
    };

    if shielded_outputs.is_empty() {
        None
    } else {
        let mut txid = TxId([0u8; 32]);
        txid.0.copy_from_slice(&tx.txHash);
        Some(WalletTx {
            txid,
            num_spends,
            num_outputs,
            shielded_outputs,
        })
    }
}

/// Returns a vector of transactions belonging to any of the given
/// ExtendedFullViewingKeys.
pub fn scan_block(block: block::CompactBlock, extfvks: &[ExtendedFullViewingKey]) -> Vec<WalletTx> {
    block
        .vtx
        .into_iter()
        .filter_map(|tx| scan_tx(tx, extfvks))
        .collect()
}

/// Returns a vector of transactions belonging to any of the given
/// ExtendedFullViewingKeys.
pub fn scan_block_from_bytes(block: &[u8], extfvks: &[ExtendedFullViewingKey]) -> Vec<WalletTx> {
    let block: block::CompactBlock =
        parse_from_bytes(block).expect("Cannot convert into a `block::CompactBlock`");

    scan_block(block, extfvks)
}
