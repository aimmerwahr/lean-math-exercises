import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace Solutions.FieldTheory.SplittingFields

open scoped Polynomial
open Polynomial


noncomputable def omega : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2


theorem q1_root_in_splitting_field {K : Type*} [Field K] (p : K[X])
    (hp : p.natDegree ≠ 0) :
    ∃ x : SplittingField p, p.eval₂ (algebraMap K (SplittingField p)) x = 0 := by
  -- A nonconstant product of linear factors has at least one linear factor, hence a root.
  obtain ⟨x, hx⟩ := (SplittingField.splits p).exists_eval_eq_zero (by
    simpa only [Polynomial.degree_map, Nat.cast_zero] using
      (Polynomial.degree_ne_of_natDegree_ne hp))
  exact ⟨x, by simpa only [Polynomial.eval₂_eq_eval_map] using hx⟩


theorem q2_roots_integral {K : Type*} [Field K] (p : K[X]) (x : SplittingField p)
    (hx : x ∈ p.rootSet (SplittingField p)) : IsIntegral K x := by
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hx
  -- A root satisfies a nonzero polynomial over `K`, so it is algebraic and hence integral.
  apply IsAlgebraic.isIntegral
  refine ⟨p, hp, ?_⟩
  exact (Polynomial.mem_rootSet_of_ne hp).mp hx


theorem q3_factor_x_cubed_sub_one : (X ^ 3 - 1 : ℚ[X]) =
    (X - 1) * (X ^ 2 + X + 1) := by
  -- Separate the rational root from the irreducible quadratic factor.
  ring


theorem q4_no_rational_root_x_sq_add_x_add_one (x : ℚ) : x ^ 2 + x + 1 ≠ 0 := by
  intro hroot
  -- Completing the square would make a nonnegative rational square equal to `-3/4`.
  have hsquare := sq_nonneg (x + 1 / 2)
  nlinarith


theorem q5_omega_quadratic_relation : omega ^ 2 + omega + 1 = 0 := by
  -- The real and imaginary parts reduce the calculation to `(√3)² = 3`.
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  apply Complex.ext <;>
    simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith


theorem q6_omega_cubed_eq_one : omega ^ 3 = 1 := by
  -- The quadratic relation is the nontrivial factor of `ω³ - 1`.
  have hquadratic := q5_omega_quadratic_relation
  have hnot_one : omega ≠ 1 := by
    intro h
    rw [h] at hquadratic
    norm_num at hquadratic
  have hfactor : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    rw [hquadratic]
    ring
  have hcubed : omega ^ 3 - 1 = 0 := by
    calc
      omega ^ 3 - 1 = (omega - 1) * (omega ^ 2 + omega + 1) := by ring
      _ = 0 := hfactor
  exact sub_eq_zero.mp hcubed


theorem q7_omega_root_x_cubed_sub_one : ((X ^ 3 - 1 : ℂ[X]).eval omega) = 0 := by
  -- Evaluating the polynomial is exactly the relation from q6.
  simpa using sub_eq_zero.mpr q6_omega_cubed_eq_one


theorem q8_omega_integral : IsIntegral ℚ omega := by
  -- The monic quadratic relation from q5 has rational coefficients.
  refine ⟨X ^ 2 + X + 1, ?_, ?_⟩
  · rw [show (X ^ 2 + X + 1 : ℚ[X]) = X ^ 2 + (X + 1) by ring]
    apply Polynomial.monic_X_pow_add
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    norm_num
  · simpa [Polynomial.aeval_def] using q5_omega_quadratic_relation


end Solutions.FieldTheory.SplittingFields
