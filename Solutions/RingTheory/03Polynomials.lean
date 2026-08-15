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


theorem q1_factor_theorem (p : K[X]) (a : K) :
    Polynomial.X - Polynomial.C a ∣ p ↔ p.eval a = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro h
    -- Division by `X - C a` has constant remainder `p(a)`.  When `a` is a root, that remainder
    -- is zero, so the division identity is the required factorization.
    refine ⟨p /ₘ (Polynomial.X - Polynomial.C a), ?_⟩
    have hmod : p %ₘ (Polynomial.X - Polynomial.C a) = 0 := by
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, h, Polynomial.C_0]
    symm
    calc
      (Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a)) =
          0 + (Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a)) := by simp
      _ = p %ₘ (Polynomial.X - Polynomial.C a) +
          (Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a)) := by rw [hmod]
      _ = p := Polynomial.modByMonic_add_div p _


theorem q2_cubic_root :
    ((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]).eval 1) = 0 := by
  norm_num


theorem q3_cubic_factor :
    (Polynomial.X - 1 : ℚ[X]) ∣ Polynomial.X ^ 3 - 2 * Polynomial.X + 1 := by
  exact q1_factor_theorem _ 1 |>.mpr q2_cubic_root


theorem q4_cubic_full_factorization :
    (Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : ℚ[X]) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X - 1) := by
  ring


theorem q5_x_sq_plus_one_factor :
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


end Solutions.RingTheory.Polynomials
