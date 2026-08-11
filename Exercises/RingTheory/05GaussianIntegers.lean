import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Exercises — RingTheory / Gaussian Integers

The Gaussian integers `ℤ[i]` have elements `a + bi` and norm `a² + b²`. The norm is
multiplicative, so it controls units and supports Euclidean division. Factorizations in `ℤ[i]`
also explain when an ordinary prime can be written as a sum of two squares.

Prove each statement yourself; the canonical proofs live in
`Solutions/RingTheory/05GaussianIntegers.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.RingTheory.GaussianIntegers

/-! ## Potentially helpful results -/
section

#check Zsqrtd.norm_mul
#check Zsqrtd.norm_eq_one_iff'
#check EuclideanDomain.div_add_mod
#check Nat.Prime.sq_add_sq

end

/-- **Question 1.**

The Gaussian norm is multiplicative.

This is an application exercise: use multiplicativity of the quadratic norm. -/
theorem q1_norm_mul (z w : GaussianInt) : (z * w).norm = z.norm * w.norm := by sorry


/-- **Question 2.**

A Gaussian integer is a unit exactly when its norm is one.

This is an application exercise: use the unit criterion for a quadratic integer of negative norm
parameter. -/
theorem q2_unit_iff_norm_one (z : GaussianInt) : z.norm = 1 ↔ IsUnit z := by sorry


/-- **Question 3.**

Gaussian integers satisfy the division-with-remainder identity.

This is an application exercise: use the Euclidean division identity. -/
theorem q3_division (z w : GaussianInt) : z / w * w + z % w = z := by sorry


/-- **Question 4.**

Five splits in the Gaussian integers: `5 = (2+i)(2-i)`. -/
theorem q4_five_splits :
    ((5 : ℤ) : GaussianInt) = (⟨2, 1⟩ : GaussianInt) * ⟨2, -1⟩ := by sorry


/-- **Question 5.**

An odd prime not congruent to `3 mod 4` is a sum of two squares.

This is an application exercise: apply Fermat's two-squares theorem for primes. -/
theorem q5_two_squares (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by sorry


/-- **Question 6.**

If a prime is reducible in `ℤ[i]`, its norm calculation produces a sum-of-two-squares
representation.

This is an application exercise: use the Gaussian-integer reducibility criterion for rational
primes. -/
theorem q6_reducible_prime_two_squares (p : ℕ) [Fact p.Prime]
    (hp : ¬ Irreducible (p : GaussianInt)) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by sorry

end Exercises.RingTheory.GaussianIntegers
