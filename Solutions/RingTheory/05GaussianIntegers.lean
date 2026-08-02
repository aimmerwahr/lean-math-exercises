import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

namespace Solutions.RingTheory.GaussianIntegers

theorem q1_norm_mul (z w : GaussianInt) : (z * w).norm = z.norm * w.norm := by
  exact Zsqrtd.norm_mul z w

theorem q2_unit_iff_norm_one (z : GaussianInt) : z.norm = 1 ↔ IsUnit z := by
  exact Zsqrtd.norm_eq_one_iff' (by norm_num) z

theorem q3_division (z w : GaussianInt) : z / w * w + z % w = z := by
  simpa [mul_comm] using EuclideanDomain.div_add_mod z w

theorem q4_five_splits :
    ((5 : ℤ) : GaussianInt) = (⟨2, 1⟩ : GaussianInt) * ⟨2, -1⟩ := by
  ext <;> norm_num

theorem q5_two_squares (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  exact Nat.Prime.sq_add_sq hp

theorem q6_reducible_prime_two_squares (p : ℕ) [Fact p.Prime]
    (hp : ¬ Irreducible (p : GaussianInt)) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  exact GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hp

end Solutions.RingTheory.GaussianIntegers
