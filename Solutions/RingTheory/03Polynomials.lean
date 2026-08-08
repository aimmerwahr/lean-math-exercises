import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

namespace Solutions.RingTheory.Polynomials

open scoped Polynomial

variable {K : Type*} [Field K]

theorem q1_degree_mul (p q : K[X]) :
    (p * q).degree = p.degree + q.degree := by
  exact Polynomial.degree_mul


theorem q2_factor_theorem (p : K[X]) (a : K) :
    Polynomial.X - Polynomial.C a ∣ p ↔ p.eval a = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro h
    refine ⟨p /ₘ (Polynomial.X - Polynomial.C a), ?_⟩
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h).symm


theorem q3_cubic_root :
    ((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]).eval 1) = 0 := by
  norm_num


theorem q4_cubic_factor :
    (Polynomial.X - 1 : ℚ[X]) ∣ Polynomial.X ^ 3 - 2 * Polynomial.X + 1 := by
  exact q2_factor_theorem _ 1 |>.mpr q3_cubic_root


theorem q5_roots_le_degree (p : K[X]) : p.roots.card ≤ p.natDegree := by
  obtain ⟨q, _, hdegree, _⟩ := Polynomial.exists_prod_multiset_X_sub_C_mul p
  exact Nat.le.intro hdegree


theorem q6_x_sq_plus_one_factor :
    (Polynomial.X ^ 2 + 1 : (ZMod 5)[X]) =
      (Polynomial.X - 2) * (Polynomial.X + 2) := by
  ring_nf
  have h : (1 : ZMod 5) = -4 := by
    change ((1 : ℤ) : ZMod 5) = ((-4 : ℤ) : ZMod 5)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  have hpoly : (1 : (ZMod 5)[X]) = -4 := by
    calc
      1 = Polynomial.C (1 : ZMod 5) := Polynomial.C_1.symm
      _ = Polynomial.C (-4 : ZMod 5) := congrArg Polynomial.C h
      _ = -Polynomial.C (4 : ZMod 5) := map_neg Polynomial.C 4
      _ = -4 := by rw [map_ofNat]
  rw [hpoly]


theorem q7_zero_function_poly [Infinite K] (p : K[X]) (h : ∀ x : K, p.eval x = 0) : p = 0 := by
  exact Polynomial.zero_of_eval_zero p h


theorem q8_irreducible_no_root (p : K[X]) (hp : p.Monic) (hdeg2 : 2 ≤ p.natDegree)
    (hdeg3 : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by
  exact hp.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg3


theorem q9_derivative_repeated_root (p : K[X]) (a : K) (hp : p ≠ 0) :
    1 < p.rootMultiplicity a ↔ p.IsRoot a ∧ p.derivative.IsRoot a := by
  exact Polynomial.one_lt_rootMultiplicity_iff_isRoot hp

end Solutions.RingTheory.Polynomials
