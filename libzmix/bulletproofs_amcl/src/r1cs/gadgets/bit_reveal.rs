use crate::errors::{R1CSError, R1CSErrorKind};
use crate::r1cs::linear_combination::AllocatedQuantity;
use crate::r1cs::{ConstraintSystem, Prover, R1CSProof, Variable, Verifier};
use amcl_wrapper::field_elem::FieldElement;
use amcl_wrapper::group_elem_g1::{G1Vector, G1};
use merlin::Transcript;
use rand::{CryptoRng, Rng};

/// Enforces that the bits of `v` covered by `reveal_mask` match `reveal_value`.
///
/// This allows the prover to reveal only selected bits of the original value
/// `v` to a verifier. The bit indexes being exposed are represented by the '1'
/// bits of `reveal_mask`, while `reveal_value` represents the original value
/// `v` after being masked.
pub fn bit_reveal_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    reveal_value: u64,
    mut reveal_mask: u64,
    n: usize,
) -> Result<(), R1CSError> {
    let mut constraint_v = vec![(v.variable, FieldElement::minus_one())];
    constraint_v.push((
        Variable::One(),
        FieldElement::from(reveal_value & reveal_mask),
    ));
    let mut exp_2 = FieldElement::one();
    for i in 0..n {
        let masked = (reveal_mask & 1) == 0;
        reveal_mask = reveal_mask >> 1;

        if masked {
            // Create low-level variables and add them to constraints
            // showing the unrevealed bits to each be either 1 or 0
            // (this is based on the positive_no gadget)
            let (a, b, o) = cs.allocate_multiplier(v.assignment.as_ref().map(|q| {
                if q.nth_bit(i) == 0 {
                    (FieldElement::one(), FieldElement::zero())
                } else {
                    (FieldElement::zero(), FieldElement::one())
                }
            }))?;

            // Enforce a * b = 0, so one of (a,b) is zero
            cs.constrain(o.into());

            // Enforce that a = 1 - b, so they both are 1 or 0.
            cs.constrain(a + (b - FieldElement::one()));

            constraint_v.push((b, exp_2.clone()));
        }

        exp_2 = &exp_2 + &exp_2;
    }

    // Enforce that -v + reveal_value + Sum(b_i * 2^i, i of masked_indexes) = 0
    // implies  Sum(b_i * 2^i, i of masked_indexes) + reveal_value = v
    cs.constrain(constraint_v.iter().collect());

    Ok(())
}

pub fn prove_bit_reveal<R: Rng + CryptoRng>(
    val: u64,
    blinding: Option<FieldElement>,
    reveal_value: u64,
    reveal_mask: u64,
    max_bits_in_val: usize,
    rng: Option<&mut R>,
    prover: &mut Prover,
) -> Result<Vec<G1>, R1CSError> {
    check_for_blindings_or_rng!(blinding, rng)?;

    let mut comms = vec![];

    let (com_v, var_v) = prover.commit(
        val.into(),
        blinding.unwrap_or_else(|| FieldElement::random_using_rng(rng.unwrap())),
    );
    let quantity_v = AllocatedQuantity {
        variable: var_v,
        assignment: Some(val.into()),
    };
    comms.push(com_v);

    bit_reveal_gadget(
        prover,
        quantity_v,
        reveal_value,
        reveal_mask,
        max_bits_in_val,
    )?;

    Ok(comms)
}

pub fn verify_bit_reveal(
    reveal_value: u64,
    reveal_mask: u64,
    max_bits_in_val: usize,
    mut commitments: Vec<G1>,
    verifier: &mut Verifier,
) -> Result<(), R1CSError> {
    let var_v = verifier.commit(commitments.remove(0));
    let quantity_v = AllocatedQuantity {
        variable: var_v,
        assignment: None,
    };

    bit_reveal_gadget(
        verifier,
        quantity_v,
        reveal_value,
        reveal_mask,
        max_bits_in_val,
    )?;
    Ok(())
}

/// Accepts the value for which the masked bits are to be revealed and the
/// randomness used in committing to that number. This randomness argument is
/// accepted so that this can be used as a sub-protocol where the protocol on
/// the upper layer will create the commitment.
pub fn gen_proof_of_bit_reveal<R: Rng + CryptoRng>(
    val: u64,
    blinding: Option<FieldElement>,
    reveal_value: u64,
    reveal_mask: u64,
    max_bits_in_val: usize,
    rng: Option<&mut R>,
    transcript_label: &'static [u8],
    g: &G1,
    h: &G1,
    G: &G1Vector,
    H: &G1Vector,
) -> Result<(R1CSProof, Vec<G1>), R1CSError> {
    let mut prover_transcript = Transcript::new(transcript_label);
    let mut prover = Prover::new(g, h, &mut prover_transcript);

    let comms = prove_bit_reveal(
        val,
        blinding,
        reveal_value,
        reveal_mask,
        max_bits_in_val,
        rng,
        &mut prover,
    )?;
    let proof = prover.prove(G, H)?;

    Ok((proof, comms))
}

pub fn verify_proof_of_bit_reveal(
    reveal_value: u64,
    reveal_mask: u64,
    max_bits_in_val: usize,
    proof: R1CSProof,
    commitments: Vec<G1>,
    transcript_label: &'static [u8],
    g: &G1,
    h: &G1,
    G: &G1Vector,
    H: &G1Vector,
) -> Result<(), R1CSError> {
    let mut verifier_transcript = Transcript::new(transcript_label);
    let mut verifier = Verifier::new(&mut verifier_transcript);
    verify_bit_reveal(
        reveal_value,
        reveal_mask,
        max_bits_in_val,
        commitments,
        &mut verifier,
    )?;
    verifier.verify(&proof, g, h, G, H)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::get_generators;
    use amcl_wrapper::group_elem::GroupElement;

    #[test]
    fn test_bit_reveal_gadget() {
        use rand::Rng;

        let mut rng = rand::thread_rng();
        let reveal_mask = 0b00111001;

        let val = rng.gen_range(0, 256);
        let reveal_value = val & reveal_mask;
        println!("val is {}, reveal_value is {}", &val, &reveal_value);
        let randomness = Some(FieldElement::random());

        let G: G1Vector = get_generators("G", 128).into();
        let H: G1Vector = get_generators("H", 128).into();
        let g = G1::from_msg_hash("g".as_bytes());
        let h = G1::from_msg_hash("h".as_bytes());

        let n = 32;

        let label = b"BitReveal";
        let (proof, commitments) = gen_proof_of_bit_reveal(
            val,
            randomness,
            reveal_value,
            reveal_mask,
            n,
            Some(&mut rng),
            label,
            &g,
            &h,
            &G,
            &H,
        )
        .unwrap();

        // println!("proof: {}", serde_json::to_string(&proof).unwrap());

        verify_proof_of_bit_reveal(
            reveal_value,
            reveal_mask,
            n,
            proof.clone(),
            commitments.clone(),
            label,
            &g,
            &h,
            &G,
            &H,
        )
        .unwrap();

        // test verify fails with a different reveal mask
        verify_proof_of_bit_reveal(
            reveal_value,
            reveal_mask | 0b110,
            n,
            proof.clone(),
            commitments.clone(),
            label,
            &g,
            &h,
            &G,
            &H,
        )
        .unwrap_err();

        // test verify fails with a different revealed value
        verify_proof_of_bit_reveal(
            if reveal_value == 0 { 1 } else { 0 },
            reveal_mask,
            n,
            proof,
            commitments,
            label,
            &g,
            &h,
            &G,
            &H,
        )
        .unwrap_err();
    }
}
