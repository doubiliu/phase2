extern crate bellman;
extern crate bls12_381;
extern crate ff;
extern crate pairing;
extern crate phase2;
extern crate proc_macro;
extern crate rand;

use std::fs::File;
use std::vec;
// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
use pairing::Engine;

use ff::PrimeField;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, Scalar};

use bellman::{Circuit, ConstraintSystem, SynthesisError};

// We're going to use the Groth16 proving system.
use bellman::groth16::{create_random_proof, prepare_verifying_key, verify_proof, Proof};
use phase2::{contains_contribution, MPCParameters};

/// This is an implementation of And-circuit
fn and<E: Engine>(xl: bool, xr: bool) -> Scalar {
    if xl && xr == true {
        Scalar::one()
    } else {
        Scalar::zero()
    }
}

/// This is our demo circuit for proving knowledge of the
/// preimage of And invocation.
struct AndDemo<'a, Scalar: PrimeField> {
    xl: Option<bool>,
    xr: Option<bool>,
    constants: &'a Option<Scalar>,
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, Scalar: PrimeField> Circuit<Scalar> for AndDemo<'a, Scalar> {
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        //print!("xl:{:?}  , xr:{:?}  ", self.xl, self.xr);
        //format check: whether xl is a boolean value
        let xl_var = cs.alloc(
            || "xl",
            || {
                if self.xl.is_some() {
                    if self.xl.unwrap() {
                        Ok(Scalar::one())
                    } else {
                        Ok(Scalar::zero())
                    }
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            },
        )?;
        //check whether xl is a boolean value
        cs.enforce(
            || "xl_boolean_constraint",
            |lc| lc + CS::one() - xl_var,
            |lc| lc + xl_var,
            |lc| lc,
        );

        //format check: whether xr is a boolean value
        let xr_var = cs.alloc(
            || "xr",
            || {
                if self.xr.is_some() {
                    if self.xr.unwrap() {
                        Ok(Scalar::one())
                    } else {
                        Ok(Scalar::zero())
                    }
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            },
        )?;

        //check whether xr is a boolean value
        cs.enforce(
            || "xr_boolean_constraint",
            |lc| lc + CS::one() - xr_var,
            |lc| lc + xr_var,
            |lc| lc,
        );

        //format check: whether constant is a boolean value
        let c_var = cs.alloc_input(
            || "c",
            || {
                let mut constants_var = false;
                if self.constants.unwrap() == Scalar::zero() {
                    constants_var = false;
                } else if self.constants.unwrap() == Scalar::one() {
                    constants_var = true;
                } else {
                    return Err(SynthesisError::AssignmentMissing);
                }
                if self.xl.is_some() && self.xr.is_some() {
                    if self.xl.unwrap() && self.xr.unwrap() {
                        Ok(Scalar::one())
                    } else {
                        Ok(Scalar::zero())
                    }
                } else {
                    Err(SynthesisError::AssignmentMissing)
                }
            },
        )?;

        //check whether a is same to b
        cs.enforce(
            || "c_and_constraint",
            |lc| lc + xl_var,
            |lc| lc + xr_var,
            |lc| lc + c_var,
        );
        Ok(())
    }
}

fn main() {
    //MPC-process
    let rng = &mut thread_rng();
    let constants = None;
    println!("Creating parameters...");
    // Create parameters for our circuit
    let mut params = {
        let c = AndDemo::<Scalar> {
            xl: None,
            xr: None,
            constants: &constants,
        };
        phase2::MPCParameters::new(c).unwrap()
    };
    //file_path
    let fp_phase2_paramters = [
        "init_old_phase2_paramter",
        "init_new_phase2_paramter",
        "first_phase2_paramter",
        "second_phase2_paramter",
    ];
    let mut my_contribution = Vec::new();

    let fp_old_params = fp_phase2_paramters[0];
    let old_params = params.clone();
    writer_params(&old_params, fp_old_params);

    for index in 0..fp_phase2_paramters.len() - 1 {
        //before contribute create
        let fp_old_params = fp_phase2_paramters[index];
        let fp_new_params = fp_phase2_paramters[index + 1];
        params.contribute(rng);
        writer_params(&params, fp_new_params);
        //next contribute verify
        let old_params = read_params(fp_old_params);
        let new_params = read_params(fp_new_params);
        let contrib = phase2::verify_contribution(&old_params, &new_params).expect("should verify");
        my_contribution.push(contrib);
    }

    let verification_result = params
        .verify(AndDemo::<Scalar> {
            xl: None,
            xr: None,
            constants: &constants,
        })
        .unwrap();
    for (index, item) in my_contribution.iter().enumerate() {
        assert!(phase2::contains_contribution(&verification_result, &item));
    }
    //Proof-process
    let params = params.get_params();
    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    println!("Creating proofs...");
    // Let's benchmark stuff!
    const SAMPLES: u32 = 50;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);
    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];
    for i in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let flag = i % 2 == 0;
        let image = and::<Bls12>(flag, true);
        proof_vec.truncate(0);
        let start = Instant::now();
        {
            // Create an instance of our circuit
            let c = AndDemo {
                xl: Some(flag),
                xr: Some(true),
                constants: &Some(image),
            };
            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, params, rng).unwrap();
            proof.write(&mut proof_vec).unwrap();
        }
        total_proving += start.elapsed();
        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        verify_proof(&pvk, &proof, &[image]).unwrap();
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);
    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);
    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}

fn read_params(file_path: &str) -> MPCParameters {
    let mut reader =
        File::open(file_path).expect(format!("file:{} open failed", file_path).as_str());
    return MPCParameters::read(reader, false).expect("params read failed");
}

fn writer_params(params: &MPCParameters, file_path: &str) {
    let mut writer =
        File::create(file_path).expect(format!("file:{} create failed", file_path).as_str());
    params.write(writer);
}
