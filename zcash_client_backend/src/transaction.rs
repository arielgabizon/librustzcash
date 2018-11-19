use failure::Error;
use pairing::Field;
use pairing::bls12_381::{Bls12, Fr};
use rand::{OsRng, Rand};
use sapling_crypto::{
    jubjub::fs::{Fs,FsRepr},
    jubjub::{Unknown,PrimeOrder,JubjubEngine,FixedGenerators,JubjubParams},
    jubjub::edwards,
    primitives::{Diversifier, Note, PaymentAddress},
    redjubjub::{PrivateKey, PublicKey, Signature},
};

use zcash_primitives::{
    merkle_tree::{CommitmentTreeWitness, IncrementalWitness},
    sapling::spend_sig,
    transaction::{
        components::{Amount, OutputDescription, SpendDescription},
        signature_hash_data, Transaction, TransactionData, SIGHASH_ALL,
    },
    JUBJUB,
};

use zcash_proofs::sapling::SaplingProvingContext;
use zip32::{ChildIndex, ExtendedFullViewingKey, ExtendedSpendingKey, OutgoingViewingKey};

use note_encryption::{Memo, SaplingNoteEncryption};
use prover::TxProver;
use pairing::PrimeField;

const DEFAULT_FEE: Amount = Amount(10000);

struct SpendDescriptionInfo {
    account_id: u32,
    diversifier: Diversifier,
    note: Note<Bls12>,
    ar: Fs,
    witness: CommitmentTreeWitness,
}

struct OutputDescriptionInfo {
    ovk: OutgoingViewingKey,
    to: PaymentAddress<Bls12>,
    note: Note<Bls12>,
    memo: Memo,
}




/// Generates a Transaction from its inputs and outputs.
pub struct Builder {
    mtx: TransactionData,
    coin_type: u32,
    fee: Amount,
    anchor: Option<Fr>,
    spends: Vec<SpendDescriptionInfo>,
    outputs: Vec<OutputDescriptionInfo>,
    change_address: Option<(OutgoingViewingKey, PaymentAddress<Bls12>)>,
}

impl Builder {
    pub fn new(coin_type: u32) -> Builder {
        Builder {
            mtx: TransactionData::new(),
            coin_type,
            fee: DEFAULT_FEE,
            anchor: None,
            spends: vec![],
            outputs: vec![],
            change_address: None,
        }
    }

    pub fn set_fee(&mut self, fee: Amount) {
        self.fee = fee;
    }

    pub fn add_sapling_spend(
        &mut self,
        account_id: u32,
        diversifier: Diversifier,
        note: Note<Bls12>,
        ar: Fs,
        witness: IncrementalWitness,
    ) -> Result<(), Error> {
        // Consistency check: all anchors must equal the first one
        if let Some(anchor) = self.anchor {
            let witness_root: Fr = witness.root().into();
            if witness_root != anchor {
                return Err(format_err!(
                    "Anchor mismatch (expected {}, got {})",
                    anchor,
                    witness_root
                ));
            }
        } else {
            self.anchor = Some(witness.root().into())
        }

        self.mtx.value_balance.0 += note.value as i64;

        self.spends.push(SpendDescriptionInfo {
            account_id,
            diversifier,
            note,
            ar,
            witness: witness.path()?,
        });

        Ok(())
    }

    pub fn add_sapling_output(
        &mut self,
        ovk: OutgoingViewingKey,
        to: PaymentAddress<Bls12>,
        value: Amount,
        memo: Option<Memo>,
    ) -> Result<(), Error> {
        let g_d = match to.g_d(&JUBJUB) {
            Some(g_d) => g_d,
            None => return Err(format_err!("Invalid target address")),
        };

        let mut rng = OsRng::new().expect("should be able to construct RNG");
        let rcm = Fs::rand(&mut rng);

        self.mtx.value_balance.0 -= value.0;

        let note = Note {
            g_d,
            pk_d: to.pk_d.clone(),
            value: value.0 as u64,
            r: rcm,
        };
        self.outputs.push(OutputDescriptionInfo {
            ovk,
            to,
            note,
            memo: memo.unwrap_or_default(),
        });

        Ok(())
    }

    pub fn build(
        mut self,
        consensus_branch_id: u32,
        master: &ExtendedSpendingKey,
        prover: impl TxProver,
    ) -> Result<Transaction, Error> {
        //
        // Consistency checks
        //

        // Valid change
        let change = self.mtx.value_balance.0 - self.fee.0;
        if change.is_negative() {
            return Err(format_err!("Change is negative: {}", change));
        }

        //
        // Change output
        //

        if change.is_positive() {
            // Send change to the specified change address. If no change address
            // was set, send change to the first Sapling address given as input.
            let change_address = if let Some(change_address) = self.change_address.take() {
                change_address
            } else if !self.spends.is_empty() {
                let xsk = ExtendedSpendingKey::from_path(
                    &master,
                    &[
                        ChildIndex::Hardened(32),
                        ChildIndex::Hardened(self.coin_type),
                        ChildIndex::Hardened(self.spends[0].account_id),
                    ],
                );
                let ovk = ExtendedFullViewingKey::from(&xsk).fvk.ovk;
                (
                    ovk,
                    PaymentAddress {
                        diversifier: self.spends[0].diversifier,
                        pk_d: self.spends[0].note.pk_d.clone(),
                    },
                )
            } else {
                return Err(format_err!("No change address"));
            };

            self.add_sapling_output(change_address.0, change_address.1, Amount(change), None)?;
        }

        //
        // Sapling spending keys
        //

        let coin_type = self.coin_type;
        let spends: Vec<_> = self
            .spends
            .into_iter()
            .map(|spend| {
                (
                    ExtendedSpendingKey::from_path(
                        &master,
                        &[
                            ChildIndex::Hardened(32),
                            ChildIndex::Hardened(coin_type),
                            ChildIndex::Hardened(spend.account_id),
                        ],
                    ),
                    spend,
                )
            }).collect();

        //
        // Sapling spends and outputs
        //

        let mut ctx = SaplingProvingContext::new();
        let anchor = self.anchor.expect("anchor was set if spends were added");

        // Create Sapling SpendDescriptions
        for (xsk, spend) in spends.iter() {
            let proof_generation_key = xsk.expsk.proof_generation_key(&JUBJUB);

            let mut nullifier = [0u8; 32];
            nullifier.copy_from_slice(&spend.note.nf(
                &proof_generation_key.into_viewing_key(&JUBJUB),
                spend.witness.position,
                &JUBJUB,
            ));

            let (zkproof, cv, rk) = prover.spend_proof(
                &mut ctx,
                proof_generation_key,
                spend.diversifier,
                spend.note.r,
                spend.ar,
                spend.note.value,
                anchor,
                spend.witness.clone(),
            )?;

            self.mtx.shielded_spends.push(SpendDescription {
                cv,
                anchor: anchor,
                nullifier,
                rk,
                zkproof,
                spend_auth_sig: Signature::blank(),
            });
        }

        // Create Sapling OutputDescriptions
        for output in self.outputs {
            let encryptor = SaplingNoteEncryption::new(
                output.ovk,
                output.note.clone(),
                output.to.clone(),
                output.memo,
            );

            let (zkproof, cv) = prover.output_proof(
                &mut ctx,
                encryptor.esk().clone(),
                output.to,
                output.note.r,
                output.note.value,
            );

            let cmu = output.note.cm(&JUBJUB);

            let enc_ciphertext = encryptor.encrypt_note_plaintext();
            let out_ciphertext = encryptor.encrypt_outgoing_plaintext(&cv, &cmu);

            let ephemeral_key = encryptor.epk().clone().into();

            self.mtx.shielded_outputs.push(OutputDescription {
                cv,
                cmu,
                ephemeral_key,
                enc_ciphertext,
                out_ciphertext,
                zkproof,
            });
        }

        //
        // Signatures
        //

        let mut sighash = [0u8; 32];
        sighash.copy_from_slice(&signature_hash_data(
            &self.mtx,
            consensus_branch_id,
            SIGHASH_ALL,
            None,
        ));

        // Create Sapling spendAuth and binding signatures
        for (i, (xsk, spend)) in spends.into_iter().enumerate() {
            self.mtx.shielded_spends[i].spend_auth_sig =
                spend_sig(PrivateKey(xsk.expsk.ask), spend.ar, &sighash, &JUBJUB);
        }
        self.mtx.binding_sig = Some(
            ctx.binding_sig(self.mtx.value_balance.0, &sighash, &JUBJUB)
                .map_err(|_| format_err!("Failed to create bindingSig"))?,
        );

        Ok(self.mtx.freeze())
    }



//pub fn aggregate_spend_signatures(
//    mut self,
//    consensus_branch_id: u32,
//    pk: PublicKey<Bls12>,
//    ask: PrivateKey<Bls12>
//) -> Result<Transaction, Error>{
//
//    let mut sighash = [0u8; 32];
//    sighash.copy_from_slice( & signature_hash_data(
//    & self.mtx,
//    consensus_branch_id,
//    SIGHASH_ALL,
//    None,
//    ));
//
//
//    pk.0.write(&mut data_to_be_signed[0..32])
//        .expect("message buffer should be 32 bytes");
//    (&mut data_to_be_signed[32..64]).copy_from_slice(&sighash[..]);
//
//    // Aggregate a signature by ask to each spend
//    for (i, (xsk, spend)) in spends.into_iter().enumerate() {
//    self.mtx.shielded_spends[i].spend_auth_sig[1].
//    spend_sig(PrivateKey(xsk.expsk.ask), spend.ar, & sighash, &JUBJUB);
//    }
//}
    // build tx but don't add the spend authorization signatures - might be good for multisig
    pub fn build_no_sign(
        mut self,
        consensus_branch_id: u32,
        master: &ExtendedSpendingKey,
        prover: impl TxProver,
    ) -> Result<Transaction, Error> {
        //
        // Consistency checks
        //

        // Valid change
        let change = self.mtx.value_balance.0 - self.fee.0;
        if change.is_negative() {
            return Err(format_err!("Change is negative: {}", change));
        }

        //
        // Change output
        //

        if change.is_positive() {
            // Send change to the specified change address. If no change address
            // was set, send change to the first Sapling address given as input.
            let change_address = if let Some(change_address) = self.change_address.take() {
                change_address
            } else if !self.spends.is_empty() {
                let xsk = ExtendedSpendingKey::from_path(
                    &master,
                    &[
                        ChildIndex::Hardened(32),
                        ChildIndex::Hardened(self.coin_type),
                        ChildIndex::Hardened(self.spends[0].account_id),
                    ],
                );
                let ovk = ExtendedFullViewingKey::from(&xsk).fvk.ovk;
                (
                    ovk,
                    PaymentAddress {
                        diversifier: self.spends[0].diversifier,
                        pk_d: self.spends[0].note.pk_d.clone(),
                    },
                )
            } else {
                return Err(format_err!("No change address"));
            };

            self.add_sapling_output(change_address.0, change_address.1, Amount(change), None)?;
        }

        //
        // Sapling spending keys
        //

        let coin_type = self.coin_type;
        let spends: Vec<_> = self
            .spends
            .into_iter()
            .map(|spend| {
                (
                    ExtendedSpendingKey::from_path(
                        &master,
                        &[
                            ChildIndex::Hardened(32),
                            ChildIndex::Hardened(coin_type),
                            ChildIndex::Hardened(spend.account_id),
                        ],
                    ),
                    spend,
                )
            }).collect();

        //
        // Sapling spends and outputs
        //

        let mut ctx = SaplingProvingContext::new();
        let anchor = self.anchor.expect("anchor was set if spends were added");

        // Create Sapling SpendDescriptions
        for (xsk, spend) in spends.iter() {
            let proof_generation_key = xsk.expsk.proof_generation_key(&JUBJUB);

            let mut nullifier = [0u8; 32];
            nullifier.copy_from_slice(&spend.note.nf(
                &proof_generation_key.into_viewing_key(&JUBJUB),
                spend.witness.position,
                &JUBJUB,
            ));

            let (zkproof, cv, rk) = prover.spend_proof(
                &mut ctx,
                proof_generation_key,
                spend.diversifier,
                spend.note.r,
                spend.ar,
                spend.note.value,
                anchor,
                spend.witness.clone(),
            )?;

            self.mtx.shielded_spends.push(SpendDescription {
                cv,
                anchor: anchor,
                nullifier,
                rk,
                zkproof,
                spend_auth_sig: Signature::blank(),
            });
        }

        // Create Sapling OutputDescriptions
        for output in self.outputs {
            let encryptor = SaplingNoteEncryption::new(
                output.ovk,
                output.note.clone(),
                output.to.clone(),
                output.memo,
            );

            let (zkproof, cv) = prover.output_proof(
                &mut ctx,
                encryptor.esk().clone(),
                output.to,
                output.note.r,
                output.note.value,
            );

            let cmu = output.note.cm(&JUBJUB);

            let enc_ciphertext = encryptor.encrypt_note_plaintext();
            let out_ciphertext = encryptor.encrypt_outgoing_plaintext(&cv, &cmu);

            let ephemeral_key = encryptor.epk().clone().into();

            self.mtx.shielded_outputs.push(OutputDescription {
                cv,
                cmu,
                ephemeral_key,
                enc_ciphertext,
                out_ciphertext,
                zkproof,
            });
        }

        //
        // Signatures
        //

        let mut sighash = [0u8; 32];
        sighash.copy_from_slice(&signature_hash_data(
            &self.mtx,
            consensus_branch_id,
            SIGHASH_ALL,
            None,
        ));

        // Create Sapling binding signature
        for (i, (xsk, spend)) in spends.into_iter().enumerate() {
            self.mtx.shielded_spends[i].spend_auth_sig =
                spend_sig(PrivateKey(xsk.expsk.ask), spend.ar, &sighash, &JUBJUB);
        }
        self.mtx.binding_sig = Some(
            ctx.binding_sig(self.mtx.value_balance.0, &sighash, &JUBJUB)
                .map_err(|_| format_err!("Failed to create bindingSig"))?,
        );

        Ok(self.mtx.freeze())
    }
}

#[cfg(test)]
mod tests {
    use pairing::PrimeField;
    use rand::{OsRng, Rand};
    use sapling_crypto::jubjub::fs::Fs;
    use sapling_crypto::{musig_comp1, musig_comp2};
    use zcash_primitives::{
        merkle_tree::{CommitmentTree, IncrementalWitness, Node},
        transaction::components::Amount,
        JUBJUB,
    };
    use zip32::{ExtendedFullViewingKey, ExtendedSpendingKey};

    use super::Builder;
    use prover::MockTxProver;



    #[test]
    fn addresses_match(){

    }

    #[test]
    fn fails_on_negative_change() {
        let mut rng = OsRng::new().expect("should be able to construct RNG");

        let master = ExtendedSpendingKey::master(&[]);

        // Fails with no inputs or outputs
        // 0.0001 t-ZEC fee
        {
            let builder = Builder::new(1);
            match builder.build(1, &master, MockTxProver) {
                Err(e) => assert_eq!(e.to_string(), "Change is negative: -10000"),
                Ok(_) => panic!("Should have failed"),
            }
        }

        let extfvk = ExtendedFullViewingKey::from(&master);
        let ovk = extfvk.fvk.ovk;
        let to = extfvk.default_address().unwrap().1;

        // Fail if there is only a Sapling output
        // 0.0005 z-ZEC out, 0.0001 t-ZEC fee
        {
            let mut builder = Builder::new(1);
            builder
                .add_sapling_output(ovk, to.clone(), Amount(50000), None)
                .unwrap();
            match builder.build(1, &master, MockTxProver) {
                Err(e) => assert_eq!(e.to_string(), "Change is negative: -60000"),
                Ok(_) => panic!("Should have failed"),
            }
        }

        let note1 = to.create_note(59999, Fs::rand(&mut rng), &JUBJUB).unwrap();
        let cm1 = Node::new(note1.cm(&JUBJUB).into_repr());
        let mut tree = CommitmentTree::new();
        tree.append(cm1).unwrap();
        let mut witness1 = IncrementalWitness::from_tree(&tree);

        // Fail if there is only a Sapling output
        // 0.0005 z-ZEC out, 0.0001 t-ZEC fee, 0.00059999 z-ZEC in
        {
            let mut builder = Builder::new(1);
            builder
                .add_sapling_spend(
                    0,
                    to.diversifier,
                    note1.clone(),
                    Fs::rand(&mut rng),
                    witness1.clone(),
                ).unwrap();
            builder
                .add_sapling_output(ovk, to.clone(), Amount(50000), None)
                .unwrap();
            match builder.build(1, &master, MockTxProver) {
                Err(e) => assert_eq!(e.to_string(), "Change is negative: -1"),
                Ok(_) => panic!("Should have failed"),
            }
        }

        let note2 = to.create_note(1, Fs::rand(&mut rng), &JUBJUB).unwrap();
        let cm2 = Node::new(note2.cm(&JUBJUB).into_repr());
        tree.append(cm2).unwrap();
        witness1.append(cm2).unwrap();
        let witness2 = IncrementalWitness::from_tree(&tree);

        // Succeeds if there is sufficient input
        // 0.0005 z-ZEC out, 0.0001 t-ZEC fee, 0.0006 z-ZEC in
        //
        // (Still fails because we are using a MockTxProver which doesn't correctly update
        // the internals of SaplingProvingContext.)
        {
            let mut builder = Builder::new(1);
            builder
                .add_sapling_spend(0, to.diversifier, note1, Fs::rand(&mut rng), witness1)
                .unwrap();
            builder
                .add_sapling_spend(0, to.diversifier, note2, Fs::rand(&mut rng), witness2)
                .unwrap();
            builder
                .add_sapling_output(ovk, to, Amount(50000), None)
                .unwrap();
            match builder.build(1, &master, MockTxProver) {
                Err(e) => assert_eq!(e.to_string(), "Failed to create bindingSig"),
                Ok(_) => panic!("Should have failed"),
            }
        }
    }
}
