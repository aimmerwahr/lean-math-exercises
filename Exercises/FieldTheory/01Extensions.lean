import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Tactic

/-!
# Exercises — FieldTheory / Extensions and Degree

An extension `L / K` is a vector space over `K`; its dimension is the degree `[L : K]`.
Minimal polynomials calculate the degree of simple algebraic extensions, while degrees multiply in
towers. These facts distinguish algebraic elements from transcendental ones.

Prove each statement yourself; the canonical proofs live in
`Solutions/FieldTheory/01Extensions.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.FieldTheory.Extensions

open scoped IntermediateField Polynomial

/-! ## Potentially helpful results -/
section

#check @Complex.ext
#check @Submodule.subset_span
#check @Submodule.smul_mem
#check @Polynomial.monic_X_pow_add_C
#check @Module.finrank_eq_card_basis
#check @Module.finrank_mul_finrank
#check @IntermediateField.finrank_eq_one_iff
#check @IntermediateField.finrank_eq_one_iff_eq_top
#check @Polynomial.eval₂_C_X

end


/-- **Question 1.**

Every complex number has unique real and imaginary coordinates: prove that
each `z : ℂ` can be written in exactly one way as `a + b * i` with `a, b : ℝ`. -/
theorem q1_complex_coordinates (z : ℂ) :
    ∃! ab : ℝ × ℝ, z = (ab.1 : ℂ) + ab.2 * Complex.I := by
  sorry


/-- **Question 2.**

If `a + bi = 0` with `a, b : ℝ`, then `a = b = 0`. -/
theorem q2_one_i_linear_independent (a b : ℝ) :
    (a : ℂ) + b * Complex.I = 0 → a = 0 ∧ b = 0 := by
  sorry


/-- **Question 3.**

The vectors `1` and `i` span `ℂ` as a real vector space.

Prove without using `Complex.basisOneI`. -/
theorem q3_one_i_spans_complex :
    Submodule.span ℝ ({(1 : ℂ), Complex.I} : Set ℂ) = ⊤ := by
  sorry


/-- **Question 4.**

The extension `ℂ / ℝ` has degree `2`.

Prove without using `Complex.finrank_real_complex` or `Complex.basisOneI`. -/
theorem q4_degree_complex_real : Module.finrank ℝ ℂ = 2 := by
  sorry


/-- **Question 5.**

The polynomial `X² + 1` vanishes at `i`. -/
theorem q5_i_root :
    (Polynomial.X ^ 2 + Polynomial.C 1 : ℝ[X]).eval₂ (algebraMap ℝ ℂ) Complex.I = 0 := by
  sorry


/-- **Question 6.**

The element `i` is integral over `ℝ`. -/
theorem q6_i_integral : IsIntegral ℝ Complex.I := by
  sorry


/-- **Question 7.**

Every `z ∈ ℂ` satisfies `z² - 2 Re(z) z + |z|² = 0`. -/
theorem q7_complex_quadratic_relation (z : ℂ) :
    z ^ 2 - ((2 * z.re : ℝ) : ℂ) * z + ((Complex.normSq z : ℝ) : ℂ) = 0 := by
  sorry


/-- **Question 8.**

Every complex number is integral over `ℝ`.

Prove directly from a quadratic relation, without using `IsAlgebraic.of_finite` or
`Algebra.IsAlgebraic.isAlgebraic`. -/
theorem q8_every_complex_integral (z : ℂ) : IsIntegral ℝ z := by
  sorry


/-- **Question 9.**

Inside `ℂ / ℝ`, the simple extension `ℝ(i)` is all of `ℂ`. -/
theorem q9_complex_is_generated_by_i :
    IntermediateField.adjoin ℝ ({Complex.I} : Set ℂ) = ⊤ := by
  sorry


/-- **Question 10.**

If `ℝ ⊆ F ⊆ ℂ`, then `F = ℝ` or `F = ℂ`.

Prove without using `IntermediateField.isSimpleOrder_of_finrank_prime`. -/
theorem q10_quadratic_extension_has_no_proper_intermediate_field (F : IntermediateField ℝ ℂ) :
    F = ⊥ ∨ F = ⊤ := by
  sorry


/-- **Question 11.**

A scalar `a` is a root of the linear polynomial `X - a`. -/
theorem q11_root_of_linear_polynomial (K : Type*) [Field K] (a : K) :
    (Polynomial.X - Polynomial.C a).eval a = 0 := by
  sorry


/-- **Question 12.**

The polynomial indeterminate `X ∈ K[X]` is transcendental over `K`.

Prove without using `Polynomial.transcendental_X`. -/
theorem q12_indeterminate_transcendental (K : Type*) [Field K] :
    Transcendental K (Polynomial.X : K[X]) := by
  sorry

end Exercises.FieldTheory.Extensions
