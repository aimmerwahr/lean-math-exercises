import Exercises.RingTheory.«02Ideals»
import Solutions.RingTheory.«02Ideals»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.Ideals.q2_first_iso_ring
  [RingHom.quotientKerEquivRange, RingHom.quotientKerEquivOfSurjective,
    RingHom.quotientKerEquivOfRightInverse]
assert_not_uses Exercises.RingTheory.Ideals.q3_quotient_domain_iff_prime
  [Ideal.Quotient.isDomain_iff_prime, Ideal.Quotient.isDomain]
assert_not_uses Exercises.RingTheory.Ideals.q4_quotient_field_iff_maximal
  [Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.Quotient.field,
    Ideal.Quotient.maximal_of_isField, Ideal.Quotient.exists_inv]
assert_not_uses Exercises.RingTheory.Ideals.q5_maximal_prime [Ideal.IsMaximal.isPrime]
assert_not_uses Exercises.RingTheory.Ideals.q7_zero_prime_not_maximal [Ideal.isPrime_bot]
assert_not_uses Exercises.RingTheory.Ideals.q8_kernel_constant_coeff [Polynomial.ker_constantCoeff]

assert_not_uses Solutions.RingTheory.Ideals.q2_first_iso_ring
  [RingHom.quotientKerEquivRange, RingHom.quotientKerEquivOfSurjective,
    RingHom.quotientKerEquivOfRightInverse]
assert_not_uses Solutions.RingTheory.Ideals.q3_quotient_domain_iff_prime
  [Ideal.Quotient.isDomain_iff_prime, Ideal.Quotient.isDomain]
assert_not_uses Solutions.RingTheory.Ideals.q4_quotient_field_iff_maximal
  [Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.Quotient.field,
    Ideal.Quotient.maximal_of_isField, Ideal.Quotient.exists_inv]
assert_not_uses Solutions.RingTheory.Ideals.q5_maximal_prime [Ideal.IsMaximal.isPrime]
assert_not_uses Solutions.RingTheory.Ideals.q7_zero_prime_not_maximal [Ideal.isPrime_bot]
assert_not_uses Solutions.RingTheory.Ideals.q8_kernel_constant_coeff [Polynomial.ker_constantCoeff]
