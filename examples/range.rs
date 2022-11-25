extern crate bellman;
extern crate bls12_381;
extern crate ff;
extern crate pairing;
extern crate phase2;
extern crate proc_macro;
extern crate rand;

use bellman::gadgets::Assignment;
use ff::PrimeField;
use std::fs::File;
use std::vec;
// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
use pairing::Engine;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, Scalar};

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, SynthesisError};

// We're going to use the Groth16 proving system.
use bellman::groth16::{create_random_proof, prepare_verifying_key, verify_proof, Proof};
use phase2::MPCParameters;

/// This is an implementation of Range-circuit
fn range<E: Engine>(b: u64, n: u64, less_or_equal: u64, less: u64) -> [Scalar; 4] {
    let mut result = [Scalar::zero(); 4];
    result[0] = b.into();
    result[1] = (1 << (n - 1)).into();
    result[2] = less.into();
    result[3] = less_or_equal.into();
    result
}

/// This is our demo circuit for proving knowledge of the
/// preimage of Range invocation.
struct RangeDemo<'a, Scalar: PrimeField> {
    a: Option<Scalar>,
    w: Option<Scalar>,
    wArray: Option<[Scalar; 4]>,
    not_all_zeros: Option<Scalar>,
    crArray: Option<[Scalar; 4]>,
    constants: &'a Option<[Scalar; 4]>,
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, Scalar: PrimeField> Circuit<Scalar> for RangeDemo<'a, Scalar> {
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a_var = self.a.unwrap();
        let b_var = self.constants.get().unwrap()[0];
        let pow2n = self.constants.get().unwrap()[1];
        let less_or_equal_var = self.constants.get().unwrap()[2];
        let less_var = self.constants.get().unwrap()[3];
        let w_var = self.w.unwrap();
        let mut wArray_var = vec![];
        let not_all_zeros_var = self.not_all_zeros.unwrap();
        let mut crArray_var = vec![];

        for i in 0..self.wArray.unwrap().len() {
            let wArray_v = cs.alloc(|| "", || Ok(*self.wArray.unwrap().get(i).unwrap()));
            wArray_var.push(wArray_v.unwrap());
        }
        for i in 0..self.crArray.unwrap().len() {
            let cArray_v = cs.alloc(|| "", || Ok(*self.crArray.unwrap().get(i).unwrap()));
            crArray_var.push(cArray_v.unwrap());
        }

        let mut a = cs.alloc_input(|| "a", || Ok(a_var))?;
        let mut b = cs.alloc_input(|| "b", || Ok(b_var))?;
        let mut w = cs.alloc(|| "w", || Ok(w_var))?;
        let mut not_all_zeros = cs.alloc(|| "not_all_zeros", || Ok(not_all_zeros_var))?;
        let mut less_or_equal = cs.alloc_input(|| "less_or_equal", || Ok(less_or_equal_var))?;
        let mut less = cs.alloc_input(|| "less", || Ok(less_var))?;

        cs.enforce(
            || "w=2^n+b-a",
            |lc| lc + w,
            |lc| lc + CS::one(),
            |lc| lc + (pow2n, CS::one()) + b - a,
        );

        let mut lc1 = Scalar::zero();
        for i in 0..wArray_var.len() {
            lc1 = lc1 + (1 << i, wArray_var[i]).into();
        }
        lc1 = lc1 - w;
        cs.enforce(
            || "2^0*w0+.......-w=0",
            |_| lc1,
            |lc| lc + CS::one(),
            |lc| lc,
        );

        for i in 0..wArray_var.len() {
            cs.enforce(
                || "w0(1-w0)=0",
                |lc| lc + wArray_var[i],
                |lc| lc + CS::one() - wArray_var[i],
                |lc| lc,
            );
        }

        cs.enforce(
            || "w0=cr0",
            |lc| lc + wArray_var[0],
            |lc| lc + CS::one(),
            |lc| lc + crArray_var[0],
        );

        for i in 1..crArray_var.len() {
            cs.enforce(
                || "(cr_(i-1)-1)(wi-1)=1-cr_i",
                |lc| lc + crArray_var[i - 1] - CS::one(),
                |lc| lc + wArray_var[i] - CS::one(),
                |lc| lc + CS::one() - crArray_var[i],
            );
        }

        cs.enforce(
            || "not_all_zeros=cr_n",
            |lc| lc + not_all_zeros,
            |lc| lc + CS::one(),
            |lc| lc + crArray_var[crArray_var.len() - 1],
        );

        cs.enforce(
            || "wn=less_or_equal*wn",
            |lc| lc + wArray_var[wArray_var.len() - 1],
            |lc| lc + less_or_equal,
            |lc| lc + wArray_var[wArray_var.len() - 1],
        );

        cs.enforce(
            || "wn*less_or_equal=less",
            |lc| lc + wArray_var[wArray_var.len() - 1],
            |lc| lc + not_all_zeros,
            |lc| lc + less,
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
        let c = RangeDemo::<Scalar> {
            a: Some(1u64.into()),
            w: Some(9u64.into()),
            wArray: Some([1u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
            not_all_zeros: Some(1u64.into()),
            crArray: Some([1u64.into(), 1u64.into(), 1u64.into(), 1u64.into()]),
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
        .verify(RangeDemo::<Scalar> {
            a: Some(1u64.into()),
            w: Some(9u64.into()),
            wArray: Some([1u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
            not_all_zeros: Some(1u64.into()),
            crArray: Some([1u64.into(), 1u64.into(), 1u64.into(), 1u64.into()]),
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
        let image = range::<Bls12>(2u64, 4u64, 1u64, 1u64);
        proof_vec.truncate(0);
        let start = Instant::now();
        {
            // Create an instance of our circuit
            let c = RangeDemo::<Scalar> {
                a: Some(1u64.into()),
                w: Some(9u64.into()),
                wArray: Some([1u64.into(), 0u64.into(), 0u64.into(), 1u64.into()]),
                not_all_zeros: Some(1u64.into()),
                crArray: Some([1u64.into(), 1u64.into(), 1u64.into(), 1u64.into()]),
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
        verify_proof(&pvk, &proof, &image).unwrap();
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
