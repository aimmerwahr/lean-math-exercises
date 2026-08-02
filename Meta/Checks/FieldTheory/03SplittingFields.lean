import Exercises.FieldTheory.«03SplittingFields»
import Solutions.FieldTheory.«03SplittingFields»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.FieldTheory.SplittingFields.q4_root_in_splitting_field
  [Polynomial.SplittingField.splits]
assert_not_uses Exercises.FieldTheory.SplittingFields.q5_roots_integral
  [IsAlgebraic.of_finite, Polynomial.IsSplittingField.instFiniteDimensionalSplittingField]
assert_not_uses Exercises.FieldTheory.SplittingFields.q11_irreducible_degree_dvd_splitting_degree
  [Polynomial.SplittingField.splits]

assert_not_uses Solutions.FieldTheory.SplittingFields.q4_root_in_splitting_field
  [Polynomial.SplittingField.splits]
assert_not_uses Solutions.FieldTheory.SplittingFields.q5_roots_integral
  [IsAlgebraic.of_finite, Polynomial.IsSplittingField.instFiniteDimensionalSplittingField]
assert_not_uses Solutions.FieldTheory.SplittingFields.q11_irreducible_degree_dvd_splitting_degree
  [Polynomial.SplittingField.splits]
