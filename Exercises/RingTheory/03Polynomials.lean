import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

/-! # Exercises — RingTheory / Polynomial Rings -/

namespace Exercises.RingTheory.Polynomials

open scoped Polynomial

variable {K : Type*} [Field K]

/-- **Question 1.** Degrees add under multiplication of nonzero polynomials over a field. -/
theorem q1_degree_mul (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).degree = p.degree + q.degree := by sorry


/-- **Question 2.** The factor theorem: `a` is a root precisely when `X - a` divides the polynomial. -/
theorem q2_factor_theorem (p : K[X]) (a : K) :
    Polynomial.X - Polynomial.C a ∣ p ↔ p.eval a = 0 := by sorry


/-- **Question 3.** A concrete cubic vanishes at `1`. -/
theorem q3_cubic_root :
    ((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]).eval 1) = 0 := by sorry


/-- **Question 4.** Consequently `X - 1` divides that cubic over `ℚ`. -/
theorem q4_cubic_factor :
    (Polynomial.X - 1 : ℚ[X]) ∣ Polynomial.X ^ 3 - 2 * Polynomial.X + 1 := by sorry


/-- **Question 5.** A polynomial has no more roots, counted with multiplicity, than its degree. -/
theorem q5_roots_le_degree (p : K[X]) : p.roots.card ≤ p.natDegree := by sorry


/-- **Question 6.** The unit group of a finite field is cyclic. -/
theorem q6_finite_field_units_cyclic [Finite K] : IsCyclic Kˣ := by sorry


/-- **Question 7.** Over an infinite field, a polynomial vanishing at every point is zero. -/
theorem q7_zero_function_poly [Infinite K] (p : K[X]) (h : ∀ x : K, p.eval x = 0) : p = 0 := by sorry


/-- **Question 8.** A monic polynomial of degree at most three is irreducible exactly when it has
no roots. -/
theorem q8_irreducible_no_root (p : K[X]) (hp : p.Monic) (hdeg : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by sorry


/-- **Question 9.** A repeated root is detected by the formal derivative. -/
theorem q9_derivative_repeated_root (p : K[X]) (a : K) (hp : p ≠ 0) :
    1 < p.rootMultiplicity a ↔ p.IsRoot a ∧ p.derivative.IsRoot a := by sorry

end Exercises.RingTheory.Polynomials
