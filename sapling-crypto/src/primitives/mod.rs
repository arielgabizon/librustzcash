use pairing::{
    Field,
    PrimeField,
    PrimeFieldRepr
};

use constants;
use util::hash_to_scalar;

use group_hash::group_hash;

use pedersen_hash::{
    pedersen_hash,
    Personalization
};

use byteorder::{
    LittleEndian,
    WriteBytesExt
};

use jubjub::{
    JubjubEngine,
    JubjubParams,
    edwards,
    PrimeOrder,
    FixedGenerators
};

use blake2_rfc::blake2s::Blake2s;

#[derive(Clone)]
pub struct ValueCommitment<E: JubjubEngine> {
    pub value: u64,
    pub randomness: E::Fs
}

impl<E: JubjubEngine> ValueCommitment<E> {
    pub fn cm(
        &self,
        params: &E::Params
    ) -> edwards::Point<E, PrimeOrder>
    {
        params.generator(FixedGenerators::ValueCommitmentValue)
              .mul(self.value, params)
              .add(
                  &params.generator(FixedGenerators::ValueCommitmentRandomness)
                  .mul(self.randomness, params),
                  params
              )
    }
}

#[derive(Clone)]
pub struct ProofGenerationKey<E: JubjubEngine> {
    pub ak: edwards::Point<E, PrimeOrder>,
    pub nsk: E::Fs
}

impl<E: JubjubEngine> ProofGenerationKey<E> {
    pub fn into_viewing_key(&self, params: &E::Params) -> ViewingKey<E> {
        ViewingKey {
            ak: self.ak.clone(),
            nk: params.generator(FixedGenerators::ProofGenerationKey)
                      .mul(self.nsk, params)
        }
    }
}

pub struct ViewingKey<E: JubjubEngine> {
    pub ak: edwards::Point<E, PrimeOrder>,
    pub nk: edwards::Point<E, PrimeOrder>
}

impl<E: JubjubEngine> ViewingKey<E> {
    pub fn rk(
        &self,
        ar: E::Fs,
        params: &E::Params
    ) -> edwards::Point<E, PrimeOrder> {
        self.ak.add(
            &params.generator(FixedGenerators::SpendingKeyGenerator)
                   .mul(ar, params),
            params
        )
    }

    pub fn ivk(&self) -> E::Fs {
        let mut preimage = [0; 64];

        self.ak.write(&mut preimage[0..32]).unwrap();
        self.nk.write(&mut preimage[32..64]).unwrap();

        let mut h = Blake2s::with_params(32, &[], &[], constants::CRH_IVK_PERSONALIZATION);
        h.update(&preimage);
        let mut h = h.finalize().as_ref().to_vec();

        // Drop the most significant five bits, so it can be interpreted as a scalar.
        h[31] &= 0b0000_0111;

        let mut e = <E::Fs as PrimeField>::Repr::default();
        e.read_le(&h[..]).unwrap();

        E::Fs::from_repr(e).expect("should be a valid scalar")
    }

    pub fn into_payment_address(
        &self,
        diversifier: Diversifier,
        params: &E::Params
    ) -> Option<PaymentAddress<E>>
    {
        diversifier.g_d(params).map(|g_d| {
            let pk_d = g_d.mul(self.ivk(), params);

            PaymentAddress {
                pk_d: pk_d,
                diversifier: diversifier
            }
        })
    }

    pub fn make_multisig_with(
        &self,
        ak_2: edwards::Point<E, PrimeOrder>,
        params: &E::Params
    ) -> ViewingKey<E>
    {   //TODO: randomize the resultant key with hash to avoid known attacks
        ViewingKey{ak: self.ak.add(&ak_2, params),nk: self.nk.clone()}
    }

    pub fn make_multisig_address_with(
        &self,
        ak_2: edwards::Point<E, PrimeOrder>,
        params: &E::Params
    ) -> PaymentAddress<E>
    {   //TODO: randomize the resultant key with hash to avoid known attacks
        ViewingKey{ak: self.ak.add(&ak_2, params),nk: self.nk.clone()}.into_payment_address(Diversifier([0u8;11]),params).unwrap()
    }
  }

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Diversifier(pub [u8; 11]);

impl Diversifier {
    pub fn g_d<E: JubjubEngine>(
        &self,
        params: &E::Params
    ) -> Option<edwards::Point<E, PrimeOrder>>
    {
        group_hash::<E>(&self.0, constants::KEY_DIVERSIFICATION_PERSONALIZATION, params)
    }
}

#[derive(Clone, Debug)]
pub struct PaymentAddress<E: JubjubEngine> {
    pub pk_d: edwards::Point<E, PrimeOrder>,
    pub diversifier: Diversifier
}

impl<E: JubjubEngine> PartialEq for PaymentAddress<E> {
    fn eq(&self, other: &Self) -> bool {
        self.pk_d == other.pk_d && self.diversifier == other.diversifier
    }
}

impl<E: JubjubEngine> PaymentAddress<E> {
    pub fn g_d(
        &self,
        params: &E::Params
    ) -> Option<edwards::Point<E, PrimeOrder>>
    {
        self.diversifier.g_d(params)
    }

    pub fn create_note(
        &self,
        value: u64,
        randomness: E::Fs,
        params: &E::Params
    ) -> Option<Note<E>>
    {
        self.g_d(params).map(|g_d| {
            Note {
                value: value,
                r: randomness,
                g_d: g_d,
                pk_d: self.pk_d.clone()
            }
        })
    }
}

#[derive(Clone, Debug)]
pub struct Note<E: JubjubEngine> {
    /// The value of the note
    pub value: u64,
    /// The diversified base of the address, GH(d)
    pub g_d: edwards::Point<E, PrimeOrder>,
    /// The public key of the address, g_d^ivk
    pub pk_d: edwards::Point<E, PrimeOrder>,
    /// The commitment randomness
    pub r: E::Fs
}

impl<E: JubjubEngine> PartialEq for Note<E> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
            && self.g_d == other.g_d
            && self.pk_d == other.pk_d
            && self.r == other.r
    }
}

impl<E: JubjubEngine> Note<E> {
    pub fn uncommitted() -> E::Fr {
        // The smallest u-coordinate that is not on the curve
        // is one.
        // TODO: This should be relocated to JubjubEngine as
        // it's specific to the curve we're using, not all
        // twisted edwards curves.
        E::Fr::one()
    }

    /// Computes the note commitment, returning the full point.
    fn cm_full_point(&self, params: &E::Params) -> edwards::Point<E, PrimeOrder>
    {
        // Calculate the note contents, as bytes
        let mut note_contents = vec![];

        // Writing the value in little endian
        (&mut note_contents).write_u64::<LittleEndian>(self.value).unwrap();

        // Write g_d
        self.g_d.write(&mut note_contents).unwrap();

        // Write pk_d
        self.pk_d.write(&mut note_contents).unwrap();

        assert_eq!(note_contents.len(), 32 + 32 + 8);

        // Compute the Pedersen hash of the note contents
        let hash_of_contents = pedersen_hash(
            Personalization::NoteCommitment,
            note_contents.into_iter()
                         .flat_map(|byte| {
                            (0..8).map(move |i| ((byte >> i) & 1) == 1)
                         }),
            params
        );

        // Compute final commitment
        params.generator(FixedGenerators::NoteCommitmentRandomness)
              .mul(self.r, params)
              .add(&hash_of_contents, params)
    }

    /// Computes the nullifier given the viewing key and
    /// note position
    pub fn nf(
        &self,
        viewing_key: &ViewingKey<E>,
        position: u64,
        params: &E::Params
    ) -> Vec<u8>
    {
        // Compute rho = cm + position.G
        let rho = self
            .cm_full_point(params)
            .add(
                &params.generator(FixedGenerators::NullifierPosition)
                       .mul(position, params),
                params
            );

        // Compute nf = BLAKE2s(nk | rho)
        let mut nf_preimage = [0u8; 64];
        viewing_key.nk.write(&mut nf_preimage[0..32]).unwrap();
        rho.write(&mut nf_preimage[32..64]).unwrap();
        let mut h = Blake2s::with_params(32, &[], &[], constants::PRF_NF_PERSONALIZATION);
        h.update(&nf_preimage);
        
        h.finalize().as_ref().to_vec()
    }

    /// Computes the note commitment
    pub fn cm(&self, params: &E::Params) -> E::Fr
    {
        // The commitment is in the prime order subgroup, so mapping the
        // commitment to the x-coordinate is an injective encoding.
        self.cm_full_point(params).into_xy().0
    }
}



/// First participant in a multisig
pub struct musig_comp1<E: JubjubEngine>{
    ask1_orig: E::Fs,
    ask1: E::Fs,
    ak1_orig: edwards::Point<E,PrimeOrder>,
    ak1: edwards::Point<E,PrimeOrder>,
    ak2: edwards::Point<E,PrimeOrder>,
    rand_factor1: E::Fs,
    rand_factor2: E::Fs,
    ak: edwards::Point<E,PrimeOrder>,
    rk: edwards::Point<E,PrimeOrder>,
    ar: E::Fs,
    r1: E::Fs,
    R1: edwards::Point<E,PrimeOrder>,
    R: edwards::Point<E,PrimeOrder>
}


/// First participant in a multisig
pub struct musig_comp2<E: JubjubEngine>{
    ask2_orig: E::Fs,
    ask2: E::Fs,
    ak2_orig: edwards::Point<E,PrimeOrder>,
    ak2: edwards::Point<E,PrimeOrder>,
    ak: edwards::Point<E,PrimeOrder>,
    rk: edwards::Point<E,PrimeOrder>,
    rand_factor1: E::Fs,
    rand_factor2: E::Fs,
    ar: E::Fs,
    r2: E::Fs,
    R2: edwards::Point<E,PrimeOrder>,
    R: edwards::Point<E,PrimeOrder>
}

impl<E: JubjubEngine> musig_comp1<E>{
    //make the correct joint ak address as in the musig paper
    pub fn init(&mut self, my_ask: E::Fs, ak2_orig: edwards::Point<E,PrimeOrder>,  params: &E::Params){
        self.ask1_orig = my_ask.clone();
        //compute original public key from original private key
        self.ak1_orig =params.generator(FixedGenerators::SpendingKeyGenerator).clone();//
        let c = self.ask1_orig;
        self.ak1_orig = self.ak1_orig.mul(self.ask1_orig, params);

        let mut t=[0u8;64 ];
        let mut s = [0u8;32];
        self.ak1_orig.write(&mut t[0..32]);
        ak2_orig.write(&mut t[33..64]);
        self.ak1_orig.write(&mut s[0..32]);
        self.rand_factor1 = hash_to_scalar::<E>(b"MULTI_SIG_ADDR",&t,&s);
        self.ask1 =  my_ask.clone();
        self.ask1.mul_assign(&self.rand_factor1);
        self.ak1 = self.ak1_orig.mul(self.rand_factor1,params);
        ak2_orig.write(&mut s[0..32]);
        self.rand_factor2 = hash_to_scalar::<E>(b"MULTI_SIG_ADDR",&t,&s);
        let ak2 = ak2_orig.mul(self.rand_factor2,params);
        self.ak = self.ak1.add(&ak2,params);
    }
}
//
impl<E: JubjubEngine> musig_comp2<E>{
    //make the correct joint ak address as in the musig paper
    pub fn init(&mut self, my_ask: E::Fs, ak1_orig: edwards::Point<E,PrimeOrder>,  params: &E::Params){
        self.ask2_orig = my_ask.clone();
        //compute original public key from original private key
        self.ak2_orig =params.generator(FixedGenerators::SpendingKeyGenerator).clone();//
        self.ak2_orig = self.ak2_orig.mul(self.ask2_orig, params);

        let mut t=[0u8;64 ];
        let mut s = [0u8;32];
        ak1_orig.write(&mut t[0..32]);
        self.ak2_orig.write(&mut t[33..64]);
        ak1_orig.write(&mut s[0..32]);
        self.rand_factor1 = hash_to_scalar::<E>(b"MULTI_SIG_ADDR",&t,&s);
        let ak1 = ak1_orig.mul(self.rand_factor1,params);
        self.ak2_orig.write(&mut s[0..32]);
        self.rand_factor2 = hash_to_scalar::<E>(b"MULTI_SIG_ADDR",&t,&s);
        self.ask2 =  my_ask.clone();
        self.ask2.mul_assign(&self.rand_factor2);
        self.ak2 = self.ak2_orig.mul(self.rand_factor2,params);
        self.ak = ak1.add(&self.ak2,params);
    }
}

#[test]
fn musig_addr_match(){

}