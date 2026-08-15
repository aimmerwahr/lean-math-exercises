import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

/-!
# Exercises — RingTheory / Factorization

This sheet uses concrete calculations to make three factorization tools do real work:
polynomial Bézout identities, Eisenstein's criterion, and norms in `ℤ[√-5]`.

Prove each statement yourself; the canonical proofs live in
`Solutions/RingTheory/04Factorization.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.RingTheory.Factorization

open scoped Polynomial

/-! ## Potentially helpful results -/
section

-- Eisenstein's criterion and its concrete principal-ideal hypotheses.
#check Polynomial.Monic.isEisensteinAt_of_mem_of_notMem
#check Ideal.span_singleton_prime
#check Ideal.mem_span_singleton

-- Norms in `ℤ[√-5]`.
#check Zsqrtd.norm_mul
#check Zsqrtd.norm_def
#check Zsqrtd.norm_eq_zero_iff

end

/-- **Question 1.**

Derive and verify the cleared-denominator Bézout identity in `ℤ[X]`.  Dividing by `250` over `ℚ`
shows that the class of `3X + 2` is invertible modulo `X³ + 2X² - 4X + 6`. -/
theorem q1_polynomial_bezout :
    27 * (Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 - 4 * Polynomial.X + 6 : ℤ[X]) +
      (-9 * Polynomial.X ^ 2 - 12 * Polynomial.X + 44) * (3 * Polynomial.X + 2) = 250 := by sorry

/-- **Question 2.**

Check Eisenstein at `(2)` coefficient by coefficient, then conclude that `X⁵ - 4X + 2` is
irreducible over `ℤ`. Coefficients are written with `C` explicitly so the integer coefficient
ring is visible. -/
theorem q2_eisenstein_x5_sub_fourX_add_two :
    Irreducible (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) := by sorry

/-- **Question 3.**

A second Eisenstein calculation, this time at `(3)`. Identify why the constant coefficient is
the decisive condition. -/
theorem q3_eisenstein_cubic :
    Irreducible (Polynomial.X ^ 3 +
      (Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X + Polynomial.C 12) : ℤ[X]) := by sorry

/-- **Question 4.**

Use Question 2 and unique factorization as an actual divisibility tool: when this polynomial
divides a product, it divides one factor. -/
theorem q4_prime_divides_a_factor (g h : ℤ[X]) :
    (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) ∣ g * h →
      (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) ∣ g ∨
        (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) ∣ h := by sorry

/-- **Question 5.**

In `ℤ[√-5]`, verify the two factorizations of `6`, compute the norms of all four nonunit factors,
and prove the two small-norm obstructions on which the usual non-unique-factorization argument
rests. -/
theorem q5_zsqrt5_two_factorizations :
    let s : ℤ√(-5) := ⟨0, 1⟩
    let α : ℤ√(-5) := 1 + s
    let β : ℤ√(-5) := 1 - s
    (6 : ℤ√(-5)) = (2 : ℤ√(-5)) * 3 ∧
      (6 : ℤ√(-5)) = α * β ∧
      (2 : ℤ√(-5)).norm = 4 ∧ (3 : ℤ√(-5)).norm = 9 ∧
      α.norm = 6 ∧ β.norm = 6 ∧
      (∀ z : ℤ√(-5), z.norm ≠ 2) ∧ (∀ z : ℤ√(-5), z.norm ≠ 3) := by sorry

end Exercises.RingTheory.Factorization
