import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-!
# Exercises — RingTheory / Gaussian Integers

The Gaussian integers `ℤ[i]` turn factorization into coordinate arithmetic. Their multiplicative
norm `N(a + bi) = a² + b²` detects units and makes concrete the three possible behaviours of a
rational prime: ramification, splitting, and remaining prime. The final Euclidean calculation
connects those coordinates back to Bézout identities and principal ideals.

Prove each statement yourself; the canonical proofs live in
`Solutions/RingTheory/05GaussianIntegers.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.RingTheory.GaussianIntegers

open scoped GaussianInt

/-- The Gaussian integer `i`. -/
def i : GaussianInt := ⟨0, 1⟩

/-! ## Potentially helpful results -/
section

-- Coordinate arithmetic and norms.
#check Zsqrtd.re_mul
#check Zsqrtd.im_mul
#check Zsqrtd.norm_def
#check Zsqrtd.norm_nonneg

-- Irreducibility, associates, and generated ideals.
#check irreducible_iff
#check Ideal.span_le
#check Ideal.mem_span_singleton

end

/-- **Question 1.**

Derive the conjugate/norm product and norm multiplicativity directly from coordinates. Then
compute the norms needed for the splitting examples. -/
theorem q1_conjugate_norm_product (z w : GaussianInt) :
    z * star z = (z.norm : GaussianInt) ∧ (z * w).norm = z.norm * w.norm ∧
      (1 + i).norm = 2 ∧ (2 + i).norm = 5 ∧ (3 + 2 * i).norm = 13 := by sorry

/-- **Question 2.**

A Gaussian integer with prime ordinary norm is irreducible. Construct a norm-one unit using its
conjugate; do not use a packaged norm/unit equivalence. -/
theorem q2_norm_prime_irreducible (p : ℕ) (hp : p.Prime) (z : GaussianInt)
    (hz : z.norm = p) : Irreducible z := by sorry

/-- **Question 3.**

The rational prime `2` ramifies: exhibit its factorization, prove `1+i` irreducible, and show
that `2` itself is reducible. -/
theorem q3_two_ramifies :
    (2 : GaussianInt) = -i * (1 + i) ^ 2 ∧ Irreducible (1 + i) ∧ ¬ Irreducible (2 : GaussianInt) := by sorry

/-- **Question 4.**

The rational prime `5` splits into two nonassociate irreducible Gaussian factors. -/
theorem q4_five_splits :
    (5 : GaussianInt) = (2 + i) * (2 - i) ∧ Irreducible (2 + i) ∧ Irreducible (2 - i) ∧
      ¬ Associated (2 + i) (2 - i) := by sorry

/-- **Question 5.**

Repeat the splitting analysis for `13`, and distinguish the factors up to associates. -/
theorem q5_thirteen_splits :
    (13 : GaussianInt) = (3 + 2 * i) * (3 - 2 * i) ∧
      Irreducible (3 + 2 * i) ∧ Irreducible (3 - 2 * i) ∧ ¬ Associated (3 + 2 * i) (3 - 2 * i) := by sorry

/-- **Question 6.**

Verify the displayed Euclidean divisions, the strict norm decrease, and the common divisor they
exhibit. -/
theorem q6_euclidean_algorithm :
    (3 - i : GaussianInt) = (-1 - i) * (2 * i) + (1 + i) ∧
      (2 * i : GaussianInt) = (1 + i) * (1 + i) ∧ (1 + i).norm < (2 * i).norm ∧
      (1 + i : GaussianInt) ∣ 3 - i ∧ (1 + i : GaussianInt) ∣ 2 * i := by sorry

/-- **Question 7.**

Turn the Euclidean computation into an explicit Bézout identity and an equality of the two
generated principal ideals. -/
theorem q7_bezout_and_principal_ideal :
    (1 + i : GaussianInt) = (3 - i) + (1 + i) * (2 * i) ∧
      Ideal.span ({(3 - i : GaussianInt), 2 * i} : Set GaussianInt) = Ideal.span ({1 + i} : Set GaussianInt) := by sorry

/-- **Question 8.**

Challenge: use the absence of a Gaussian integer of norm `3` to prove that `3` is irreducible,
then prime. -/
theorem q8_three_is_irreducible_and_prime :
    (∀ z : GaussianInt, z.norm ≠ 3) ∧ Irreducible (3 : GaussianInt) ∧ Prime (3 : GaussianInt) := by sorry

end Exercises.RingTheory.GaussianIntegers
