import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-! # Exercises — RingTheory / Gaussian Integers -/

namespace Exercises.RingTheory.GaussianIntegers

/-- **Question 1.** The Gaussian norm is multiplicative. -/
theorem q1_norm_mul (z w : GaussianInt) : (z * w).norm = z.norm * w.norm := by sorry


/-- **Question 2.** A Gaussian integer is a unit exactly when its norm is one. -/
theorem q2_unit_iff_norm_one (z : GaussianInt) : z.norm = 1 ↔ IsUnit z := by sorry


/-- **Question 3.** Gaussian integers admit Euclidean division. -/
theorem q3_division (z w : GaussianInt) : z / w * w + z % w = z := by sorry


/-- **Question 4.** Five splits in the Gaussian integers: `5 = (2+i)(2-i)`. -/
theorem q4_five_splits :
    ((5 : ℤ) : GaussianInt) = (⟨2, 1⟩ : GaussianInt) * ⟨2, -1⟩ := by sorry


/-- **Question 5.** An odd prime not congruent to `3 mod 4` is a sum of two squares. -/
theorem q5_two_squares (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by sorry


/-- **Question 6.** If a prime is reducible in `ℤ[i]`, its norm calculation produces a sum of two
squares representation. -/
theorem q6_reducible_prime_two_squares (p : ℕ) [Fact p.Prime]
    (hp : ¬ Irreducible (p : GaussianInt)) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by sorry

end Exercises.RingTheory.GaussianIntegers
