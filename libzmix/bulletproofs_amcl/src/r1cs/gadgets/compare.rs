use crate::errors::R1CSError;
use crate::r1cs::linear_combination::AllocatedQuantity;
use crate::r1cs::{ConstraintSystem, Variable};
use amcl_wrapper::field_elem::FieldElement;

pub fn to_bits<CS: ConstraintSystem>(
    cs: &mut CS,
    v: AllocatedQuantity,
    n: usize,
) -> Result<Vec<Variable>, R1CSError> {
    let mut constraint_v = vec![(v.variable, FieldElement::minus_one())];
    let mut exp_2 = FieldElement::one();
    let mut bits = vec![];

    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v.assignment.as_ref().map(|q| {
            if (q.shift_right(i)).is_odd() {
                (FieldElement::zero(), FieldElement::one())
            } else {
                (FieldElement::one(), FieldElement::zero())
            }
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - FieldElement::one()));

        constraint_v.push((b, exp_2.clone()));
        exp_2 = &exp_2 + &exp_2;
        bits.push(b);
    }

    // Enforce that -v + Sum(b_i * 2^i, i = 0..n-1) = 0 => Sum(b_i * 2^i, i = 0..n-1) = v
    cs.constrain(constraint_v.iter().collect());

    Ok(bits)
}

pub fn greater_than_bits_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    a: Vec<Variable>,
    b: Vec<Variable>,
    n: usize,
    with_equal: bool,
) -> Result<(), R1CSError> {
    debug_assert_ne!(n, 0);
    debug_assert_eq!(a.len(), n);
    debug_assert_eq!(b.len(), n);

    // MSB: constrain (a - b)(1 - (a - b)) == 0  --> a - b in {0,1} --> a >= b
    // set carry to (1 - (a - b))  --> carry = 0 if a > b, else 1
    let diff = a[n - 1] - b[n - 1];
    let (_, mut carry, o) = cs.multiply(diff.clone(), Variable::One() - diff);
    cs.constrain(o.into());

    for i in (0..n - 1).rev() {
        // if carry was previously set to 0 then a > b is already proven
        // set next carry = carry * (1 - (a - b))
        // (a - b)*(next carry) == 0  --> a[i] >= b[i]  or carry = 0
        let (_, _, next_carry) = cs.multiply(carry.into(), Variable::One() + b[i] - a[i]);
        carry = next_carry;
        let (_, _, o) = cs.multiply(a[i] - b[i], carry.into());
        cs.constrain(o.into());
    }

    if !with_equal {
        // if a > b, then a[i] > b[i] for some i, which changes carry to 0
        cs.constrain(carry.into());
    }

    Ok(())
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CompareOp {
    GreaterThan,
    GreaterThanEq,
    LessThan,
    LessThanEq,
}

impl CompareOp {
    pub fn as_str(&self) -> &str {
        std::str::from_utf8(self.label()).unwrap()
    }

    pub fn label(&self) -> &'static [u8] {
        match self {
            Self::GreaterThan => b"CompareGt",
            Self::GreaterThanEq => b"CompareGte",
            Self::LessThan => b"CompareLt",
            Self::LessThanEq => b"CompareLte",
        }
    }
}

pub fn compare_bits_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    a: Vec<Variable>,
    b: Vec<Variable>,
    op: CompareOp,
    bits: usize,
) -> Result<(), R1CSError> {
    let (a, b, eq) = match op {
        CompareOp::GreaterThan => (a, b, false),
        CompareOp::GreaterThanEq => (a, b, true),
        CompareOp::LessThan => (b, a, false),
        CompareOp::LessThanEq => (b, a, true),
    };

    greater_than_bits_gadget(cs, a, b, bits, eq)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs::{Prover, R1CSProof, Verifier};
    use crate::utils::get_generators;
    use amcl_wrapper::group_elem::GroupElement;
    use amcl_wrapper::group_elem_g1::{G1Vector, G1};
    use merlin::Transcript;

    pub fn prove_test_compare(
        a: u32,
        b: u32,
        op: CompareOp,
        transcript_label: &'static [u8],
        g: &G1,
        h: &G1,
        G: &G1Vector,
        H: &G1Vector,
    ) -> Result<(R1CSProof, Vec<G1>), R1CSError> {
        let mut prover_transcript = Transcript::new(transcript_label);
        let mut prover = Prover::new(g, h, &mut prover_transcript);
        let mut comms = vec![];
        let bits = 32;

        let (com_a, var_a) = prover.commit(a.into(), FieldElement::random());
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: Some(a.into()),
        };
        comms.push(com_a);

        let (com_b, var_b) = prover.commit(b.into(), FieldElement::random());
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: Some(b.into()),
        };
        comms.push(com_b);

        let bits_a = to_bits(&mut prover, quantity_a, bits)?;
        let bits_b = to_bits(&mut prover, quantity_b, bits)?;

        compare_bits_gadget(&mut prover, bits_a, bits_b, op, bits)?;

        let proof = prover.prove(G, H)?;

        Ok((proof, comms))
    }

    pub fn verify_test_compare(
        op: CompareOp,
        proof: R1CSProof,
        mut commitments: Vec<G1>,
        transcript_label: &'static [u8],
        g: &G1,
        h: &G1,
        G: &G1Vector,
        H: &G1Vector,
    ) -> Result<(), R1CSError> {
        let mut verifier_transcript = Transcript::new(transcript_label);
        let mut verifier = Verifier::new(&mut verifier_transcript);
        let bits = 32;

        let var_a = verifier.commit(commitments.remove(0));
        let quantity_a = AllocatedQuantity {
            variable: var_a,
            assignment: None,
        };

        let var_b = verifier.commit(commitments.remove(0));
        let quantity_b = AllocatedQuantity {
            variable: var_b,
            assignment: None,
        };

        let bits_a = to_bits(&mut verifier, quantity_a, bits)?;
        let bits_b = to_bits(&mut verifier, quantity_b, bits)?;

        compare_bits_gadget(&mut verifier, bits_a, bits_b, op, bits)?;

        verifier.verify(&proof, g, h, G, H)
    }

    #[test]
    fn test_compare_valid() {
        let G: G1Vector = get_generators("G", 128).into();
        let H: G1Vector = get_generators("H", 128).into();
        let g = G1::from_msg_hash("g".as_bytes());
        let h = G1::from_msg_hash("h".as_bytes());

        let checks: &[(u32, u32, CompareOp)] = &[
            (100, 101, CompareOp::LessThan),
            (100, 100, CompareOp::LessThanEq),
            (100, 101, CompareOp::LessThanEq),
            (101, 100, CompareOp::GreaterThan),
            (100, 100, CompareOp::GreaterThanEq),
            (101, 100, CompareOp::GreaterThanEq),
        ];

        for (a, b, op) in checks {
            let label = op.label();
            let (proof, commitments) =
                prove_test_compare(*a, *b, *op, label, &g, &h, &G, &H).unwrap();

            assert!(verify_test_compare(*op, proof, commitments, label, &g, &h, &G, &H).is_ok());
            println!("proof ok: {} {} {}", a, b, op.as_str());
        }

        // for a in 0..100 {
        //     let b = 101;
        //     let op = CompareOp::LessThan;
        //     let label = op.label();

        //     let (proof, commitments) = prove_test_compare(a, b, op, label, &g, &h, &G, &H).unwrap();
        //     assert!(verify_test_compare(op, proof, commitments, label, &g, &h, &G, &H).is_ok());
        //     println!("proof ok: {} {} {}", a, b, op.as_str());
        // }
    }

    #[test]
    fn test_compare_invalid() {
        let G: G1Vector = get_generators("G", 128).into();
        let H: G1Vector = get_generators("H", 128).into();
        let g = G1::from_msg_hash("g".as_bytes());
        let h = G1::from_msg_hash("h".as_bytes());

        let checks: &[(u32, u32, CompareOp)] = &[
            (100, 100, CompareOp::LessThan),
            (101, 100, CompareOp::LessThan),
            (101, 100, CompareOp::LessThanEq),
            (100, 100, CompareOp::GreaterThan),
            (100, 101, CompareOp::GreaterThan),
            (100, 101, CompareOp::GreaterThanEq),
        ];

        for (a, b, op) in checks {
            let label = op.label();
            let (proof, commitments) =
                prove_test_compare(*a, *b, *op, label, &g, &h, &G, &H).unwrap();

            assert!(verify_test_compare(*op, proof, commitments, label, &g, &h, &G, &H).is_err());
            println!("proof fails as expected: {} {} {}", a, b, op.as_str());
        }

        // for a in 0..100 {
        //     let b = 101;
        //     let op = CompareOp::GreaterThan;
        //     let label = op.label();

        //     let (proof, commitments) = prove_test_compare(a, b, op, label, &g, &h, &G, &H).unwrap();
        //     assert!(verify_test_compare(op, proof, commitments, label, &g, &h, &G, &H).is_err());
        //     println!("proof ok: {} {} {}", a, b, op.as_str());
        // }
    }
}
