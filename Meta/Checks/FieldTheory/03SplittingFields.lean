import Exercises.FieldTheory.«03SplittingFields»
import Solutions.FieldTheory.«03SplittingFields»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.FieldTheory.SplittingFields.q2_roots_integral
  [IsAlgebraic.of_finite, Polynomial.IsSplittingField.instFiniteDimensionalSplittingField]

assert_not_uses Solutions.FieldTheory.SplittingFields.q2_roots_integral
  [IsAlgebraic.of_finite, Polynomial.IsSplittingField.instFiniteDimensionalSplittingField]
