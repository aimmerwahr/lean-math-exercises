import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

/-!
# Exercises — RingTheory / Polynomial Rings

Over a field `K`, polynomials admit division with remainder. Evaluation at a point turns
divisibility by `X - a` into a question about whether the value at `a` is zero. The resulting
control of roots constrains factorization, irreducibility, and polynomial functions.

Prove each statement yourself; the canonical proofs live in
`Solutions/RingTheory/03Polynomials.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.RingTheory.Polynomials

open scoped Polynomial

variable {K : Type*} [Field K]

/-! ## Potentially helpful results -/
section

#check @Polynomial.modByMonic_add_div
#check @Polynomial.modByMonic_X_sub_C_eq_C_eval

end


/-- **Question 1.**

The factor theorem: `a` is a root precisely when `X - a` divides the polynomial.

For the reverse implication, use the quotient on division by the monic polynomial `X - C a`.
Prove without using `Polynomial.dvd_iff_isRoot`. -/
theorem q1_factor_theorem (p : K[X]) (a : K) :
    Polynomial.X - Polynomial.C a ∣ p ↔ p.eval a = 0 := by
  sorry


/-- **Question 2.**

A concrete cubic vanishes at `1`. -/
theorem q2_cubic_root :
    ((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]).eval 1) = 0 := by
  sorry


/-- **Question 3.**

Use the factor theorem to turn the calculation in Question 2 into a factorization. -/
theorem q3_cubic_factor :
    (Polynomial.X - 1 : ℚ[X]) ∣ Polynomial.X ^ 3 - 2 * Polynomial.X + 1 := by
  sorry


/-- **Question 4.**

Complete the concrete factorization obtained from Question 3. -/
theorem q4_cubic_full_factorization :
    (Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X - 1) := by
  sorry


/-- **Question 5.**

Over the field with five elements, `X² + 1` splits into two linear factors. -/
theorem q5_x_sq_plus_one_factor :
    (Polynomial.X ^ 2 + 1 : (ZMod 5)[X]) =
      (Polynomial.X - 2) * (Polynomial.X + 2) := by
  sorry


end Exercises.RingTheory.Polynomials
