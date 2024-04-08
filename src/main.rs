#![allow(non_camel_case_types)]

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::{pairing::Pairing, scalar_mul::ScalarMul};
use ark_ff::{Field, One, UniformRand};
use ark_poly::{
    univariate::{DenseOrSparsePolynomial, DensePolynomial as DensePoly},
    DenseUVPolynomial, Polynomial,
};
use ark_std::{
    marker::PhantomData,
    ops::{Div, Mul, Sub},
    rand::RngCore,
    test_rng, vec,
};

pub mod utils;

type UniPoly381 = DensePoly<<Bls12_381 as Pairing>::ScalarField>;
type KZG_Bls12_381 = Kzg<Bls12_381, UniPoly381>;

struct Kzg<E: Pairing, P: DenseUVPolynomial<E::ScalarField>> {
    _engine: PhantomData<E>,
    _poly: PhantomData<P>,
}

struct UniversalParams<E: Pairing> {
    g: E::G1Affine,
    g_mul_powers_of_alpha: Vec<E::G1Affine>,
    h: E::G2Affine,
    h_alpha: E::G2Affine,
}

impl<E, P> Kzg<E, P>
where
    E: Pairing,
    P: DenseUVPolynomial<E::ScalarField, Point = E::ScalarField>,
    for<'a, 'b> &'a P: Div<&'b P, Output = P>,
    for<'a, 'b> &'a P: Sub<&'b P, Output = P>,
{
    fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> UniversalParams<E> {
        let alpha = E::ScalarField::rand(rng);
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);

        // powers_of_alpha = [1, a, a^2, ..., a^(max_degree)], len = max_degree + 1
        let mut powers_of_alpha = vec![E::ScalarField::one()];
        let mut cur = alpha;
        for _ in 0..max_degree {
            powers_of_alpha.push(cur);
            cur *= &alpha;
        }
        // g_mul_powers_of_alpha = [g, g * a, g * a^2, ..., g * a^(max_degree)], len = max_degree + 1
        let g_mul_powers_of_alpha = g.batch_mul(&powers_of_alpha[0..=max_degree]);

        // TODO: use successors is more elegant?
        // How to best convert Vec<<E as Pairing>::G1> to Vec<<E as Pairing>::G1Affine>?
        // use std::iter::successors;
        // g_mul_powers_of_alpha2 = [g, g * a, g * a^2, ..., g * a^(max_degree)], len = max_degree + 1
        // let g_mul_powers_of_alpha2 = successors(Some(g), |g| Some(g.mul(&alpha)))
        //     .take(max_degree + 1)
        //     .collect::<Vec<<E as Pairing>::G1>>();
        // let b: Vec<<E as Pairing>::G1Affine> = g_mul_powers_of_alpha2;
        // assert_eq!(g_mul_powers_of_alpha, g_mul_powers_of_alpha2);

        UniversalParams {
            g: g.into(),
            g_mul_powers_of_alpha,
            h: h.into(),
            h_alpha: (h * alpha).into(),
        }
    }

    fn commit(g_mul_powers_of_alpha: Vec<E::G1Affine>, polynomial: P) -> E::G1Affine {
        assert!(
            polynomial.degree() < g_mul_powers_of_alpha.len(),
            "Degree of polynomial must be < length of g_mul_powers_of_alpha"
        );

        // println!("g_mul_powers_of_alpha: {:?}", g_mul_powers_of_alpha);
        // println!("polynomial.coeffs(): {:?}", polynomial.coeffs());

        // TODO use MSM functions
        // commitment = sum (g_mul_powers_of_alpha * coefficients)
        let c = g_mul_powers_of_alpha
            .iter()
            .zip(polynomial.coeffs().iter())
            .map(|(g, p)| *g * p)
            .sum::<E::G1>()
            .into();
        // println!("commitment: {:?}", c);
        c
    }

    fn open(g_mul_powers_of_alpha: &[E::G1Affine], polynomial: &P, point: P::Point) -> E::G1Affine {
        // dividend = phi(x) - phi(point)
        let dividend = polynomial - &P::from_coefficients_slice(&[polynomial.evaluate(&point)]);
        // divisor = x - point
        let divisor = P::from_coefficients_slice(&[-point, E::ScalarField::ONE]);

        // this doesn't give remainder
        // let quotient: P = &dividend / &divisor;

        // TODO: How to best convert P to DensePoly?
        // let quotient_1 = DensePoly::from_coefficients_slice(quotient.coeffs());
        let dividend_densepoly = DensePoly::from_coefficients_slice(dividend.coeffs());
        let divisor_densepoly = DensePoly::from_coefficients_slice(divisor.coeffs());
        let (quotient, remainder) = DenseOrSparsePolynomial::from(dividend_densepoly)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(divisor_densepoly))
            .unwrap();
        // assert_eq!(quotient_1, quotient_2);

        // Check remainder is zero
        assert_eq!(remainder.len(), 0, "Remainder is not zero");

        // proof = SumProduct(g_mul_powers_of_alpha * quotient)
        g_mul_powers_of_alpha
            .iter()
            .zip(quotient.coeffs().iter())
            .map(|(g, q)| *g * q)
            .sum::<E::G1>()
            .into()
    }

    fn verify(
        params: UniversalParams<E>,
        point: P::Point,
        evaluation: E::ScalarField,
        commitment: E::G1Affine,
        proof: E::G1Affine,
    ) -> bool {
        // verify e(proof, h_alpha - point * h) == e(commitment - g * evaluation, h)
        let pairing1 = E::pairing(proof, params.h_alpha - (params.h.mul(&point)));
        let pairing2 = E::pairing(commitment - (params.g.mul(evaluation)), params.h);

        pairing1 == pairing2
    }

    // TODO Batch Open and Verify
}

fn main() {
    // Create trusted setup parameters
    let max_degree = 5;
    let rng = &mut test_rng();
    let params = KZG_Bls12_381::setup(max_degree, rng);

    // Create polynomial
    let degree = max_degree - 2;
    let polynomial = UniPoly381::rand(degree, rng);

    // Commit polynomial
    let commitment =
        KZG_Bls12_381::commit(params.g_mul_powers_of_alpha.clone(), polynomial.clone());

    // Open polynomial
    let point: Fr = Fr::rand(rng);
    let proof = KZG_Bls12_381::open(&params.g_mul_powers_of_alpha, &polynomial, point);

    // Perform verification
    let evaluation = polynomial.evaluate(&point);
    let verification = KZG_Bls12_381::verify(params, point, evaluation, commitment, proof);

    println!("Verification: {}", verification);
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::test_rng;

    #[test]
    fn test_kzg_verify() {
        let max_degree = 4;
        let rng = &mut test_rng();
        let params = KZG_Bls12_381::setup(max_degree, rng);

        let degree = max_degree;
        let polynomial = UniPoly381::rand(degree, rng);
        let commitment =
            KZG_Bls12_381::commit(params.g_mul_powers_of_alpha.clone(), polynomial.clone());

        let point: Fr = Fr::rand(rng);
        let proof = KZG_Bls12_381::open(&params.g_mul_powers_of_alpha, &polynomial, point);

        let evaluation = polynomial.evaluate(&point);
        let verification = KZG_Bls12_381::verify(params, point, evaluation, commitment, proof);

        assert!(verification);
    }
}
