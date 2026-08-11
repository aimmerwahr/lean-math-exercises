import Exercises.FieldTheory.«01Extensions»
import Solutions.FieldTheory.«01Extensions»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.FieldTheory.Extensions.q4_degree_complex_real
  [Complex.finrank_real_complex, Complex.basisOneI]
assert_not_uses Exercises.FieldTheory.Extensions.q8_every_complex_integral
  [IsAlgebraic.of_finite, Algebra.IsAlgebraic.isAlgebraic]
assert_not_uses Exercises.FieldTheory.Extensions.q10_quadratic_extension_has_no_proper_intermediate_field
  [IntermediateField.isSimpleOrder_of_finrank_prime]
assert_not_uses Exercises.FieldTheory.Extensions.q12_indeterminate_transcendental
  [Polynomial.transcendental_X]

assert_not_uses Solutions.FieldTheory.Extensions.q4_degree_complex_real
  [Complex.finrank_real_complex, Complex.basisOneI]
assert_not_uses Solutions.FieldTheory.Extensions.q8_every_complex_integral
  [IsAlgebraic.of_finite, Algebra.IsAlgebraic.isAlgebraic]
assert_not_uses Solutions.FieldTheory.Extensions.q10_quadratic_extension_has_no_proper_intermediate_field
  [IntermediateField.isSimpleOrder_of_finrank_prime]
assert_not_uses Solutions.FieldTheory.Extensions.q12_indeterminate_transcendental
  [Polynomial.transcendental_X]
