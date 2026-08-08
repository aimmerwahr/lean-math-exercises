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

#check Polynomial.degree_mul
#check Polynomial.mul_divByMonic_eq_iff_isRoot
#check Polynomial.exists_prod_multiset_X_sub_C_mul
#check Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
#check Polynomial.one_lt_rootMultiplicity_iff_isRoot

end

/-- **Question 1.**

Degrees add under multiplication of polynomials over a field.

This is an application exercise: use the degree formula for a product. -/
theorem q1_degree_mul (p q : K[X]) :
    (p * q).degree = p.degree + q.degree := by sorry


/-- **Question 2.**

The factor theorem: `a` is a root precisely when `X - a` divides the polynomial.

For the reverse implication, use the quotient on division by the monic polynomial `X - C a`.
Prove without using `Polynomial.dvd_iff_isRoot`. -/
theorem q2_factor_theorem (p : K[X]) (a : K) :
    Polynomial.X - Polynomial.C a ∣ p ↔ p.eval a = 0 := by sorry


/-- **Question 3.**

A concrete cubic vanishes at `1`. -/
theorem q3_cubic_root :
    ((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]).eval 1) = 0 := by sorry


/-- **Question 4.**

Use the factor theorem to turn the calculation in Question 3 into a factorization. -/
theorem q4_cubic_factor :
    (Polynomial.X - 1 : ℚ[X]) ∣ Polynomial.X ^ 3 - 2 * Polynomial.X + 1 := by sorry


/-- **Question 5.**

A polynomial has no more roots, counted with multiplicity, than its degree.

Factor off all of its roots, then compare the degree of the remaining factor. Prove without using
`Polynomial.card_roots'`. -/
theorem q5_roots_le_degree (p : K[X]) : p.roots.card ≤ p.natDegree := by sorry


/-- **Question 6.**

Over the field with five elements, `X² + 1` splits into two linear factors. -/
theorem q6_x_sq_plus_one_factor :
    (Polynomial.X ^ 2 + 1 : (ZMod 5)[X]) =
      (Polynomial.X - 2) * (Polynomial.X + 2) := by sorry


/-- **Question 7.**

Over an infinite field, a polynomial vanishing at every point is zero.

This is an application exercise: use the theorem that a polynomial function on an infinite field
determines its polynomial. -/
theorem q7_zero_function_poly [Infinite K] (p : K[X]) (h : ∀ x : K, p.eval x = 0) : p = 0 := by sorry


/-- **Question 8.**

A monic polynomial of degree two or three is irreducible exactly when it has no roots.

This is an application exercise: use the low-degree irreducibility criterion. -/
theorem q8_irreducible_no_root (p : K[X]) (hp : p.Monic) (hdeg2 : 2 ≤ p.natDegree)
    (hdeg3 : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by sorry


/-- **Question 9.**

A repeated root is detected by the formal derivative: a root has multiplicity at least two exactly
when both the polynomial and its derivative vanish there.

This is an application exercise: use the repeated-root criterion for the formal derivative. -/
theorem q9_derivative_repeated_root (p : K[X]) (a : K) (hp : p ≠ 0) :
    1 < p.rootMultiplicity a ↔ p.IsRoot a ∧ p.derivative.IsRoot a := by sorry

end Exercises.RingTheory.Polynomials
