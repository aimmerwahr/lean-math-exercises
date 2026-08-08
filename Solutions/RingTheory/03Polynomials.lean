import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

namespace Solutions.RingTheory.Polynomials

open scoped Polynomial

variable {K : Type*} [Field K]

theorem q1_degree_mul (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).degree = p.degree + q.degree := by
  exact Polynomial.degree_mul


theorem q2_factor_theorem (p : K[X]) (a : K) :
    Polynomial.X - Polynomial.C a ∣ p ↔ p.eval a = 0 := by
  exact Polynomial.dvd_iff_isRoot


theorem q3_cubic_root :
    ((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]).eval 1) = 0 := by
  norm_num


theorem q4_cubic_factor :
    (Polynomial.X - 1 : ℚ[X]) ∣ Polynomial.X ^ 3 - 2 * Polynomial.X + 1 := by
  exact q2_factor_theorem _ 1 |>.mpr q3_cubic_root


theorem q5_roots_le_degree (p : K[X]) : p.roots.card ≤ p.natDegree := by
  exact Polynomial.card_roots' p


theorem q6_finite_field_units_cyclic [Finite K] : IsCyclic Kˣ := by
  infer_instance


theorem q7_zero_function_poly [Infinite K] (p : K[X]) (h : ∀ x : K, p.eval x = 0) : p = 0 := by
  exact Polynomial.eq_zero_of_forall_eval_zero h


theorem q8_irreducible_no_root (p : K[X]) (hp : p.Monic) (hdeg : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by
  exact hp.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg


theorem q9_derivative_repeated_root (p : K[X]) (a : K) (hp : p ≠ 0) :
    1 < p.rootMultiplicity a ↔ p.IsRoot a ∧ p.derivative.IsRoot a := by
  exact Polynomial.one_lt_rootMultiplicity_iff_isRoot hp

end Solutions.RingTheory.Polynomials
