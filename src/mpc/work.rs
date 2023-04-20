// For randomness (during paramgen and proof generation)
use rand::RngCore;
// For IO
use std::{fs, fs::File, io};
// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::Scalar;
// We're going to use the Groth16 proving system.
use bellman::{Circuit, SynthesisError};
use super::{contains_contribution, verify_contribution, MPCParameters};

/// We will provide some simplified interfaces of the MPC process here to facilitate the calling of external programs
/// Of course, also refer to the case in the test sample, where we have used these interfaces to build a demo
pub struct MPCWork {
    pub params: MPCParameters,
}

impl MPCWork {
    /// create new MPC process
    pub fn new<C: Circuit<Scalar>>(circuit: C) -> Result<MPCWork, SynthesisError> {
        let params = MPCParameters::new(circuit).unwrap();
        Ok(MPCWork { params: params })
    }

    /// read parameters from file
    pub fn read_params_from(file_path: &str) -> io::Result<MPCWork> {
        let reader =
            File::open(file_path).expect(format!("file:{} open failed", file_path).as_str());
        let params = MPCParameters::read(reader, false).expect("params read failed");
        Ok(MPCWork { params: params })
    }

    /// serialized parameters to a file
    pub fn write_params_to(&self, file_path: &str) {
        let writer =
            File::create(file_path).expect(format!("file:{} create failed", file_path).as_str());
        assert!(self.params.write(writer).is_ok());
    }

    /// update parameters
    pub fn contribute<R: RngCore>(&mut self, rng: &mut R) -> [u8; 64] {
        let old_params = self.params.clone();
        let mut new_params = self.params.clone();
        new_params.contribute(rng);
        let contrib =
            verify_contribution(&old_params, &new_params).expect("contribution verify fail");
        self.params = new_params;
        contrib
    }

    /// verify new parameters
    pub fn verify_contribution<C: Circuit<Scalar>>(&self, circuit: C, contrib: [u8; 64]) {
        let verification_result = self.params.verify(circuit).unwrap();
        assert!(contains_contribution(&verification_result, &contrib))
    }
}

pub fn clean_params(file_path: &str) {
    fs::remove_file(file_path).expect(format!("file:{} remove failed", file_path).as_str());
}
