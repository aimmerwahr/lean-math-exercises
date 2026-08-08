import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.Determinants

open Matrix

theorem q1_det_2x2 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det = -2 := by
  norm_num [Matrix.det_fin_two_of]


theorem q2_det_3x3 :
    (!![2, 0, 1; 1, 3, 2; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = 3 := by
  simp [Matrix.det_fin_three]; norm_num


theorem q3_det_mul_concrete :
    ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![5, 6; 7, 8]).det
      = (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det * (!![5, 6; 7, 8]).det := by
  -- Left side: determinant of the product matrix. Right side: product of the two determinants.
  -- Both come out to `4`.
  norm_num [Matrix.mul_fin_two, Matrix.det_fin_two_of]


theorem q4_det_triangular :
    (!![2, 5; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 2 * 3 ∧
    (!![1, 7; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  constructor <;> norm_num [Matrix.det_fin_two_of]


theorem q5_vandermonde (x y z : ℝ) :
    (!![1, x; 1, y] : Matrix (Fin 2) (Fin 2) ℝ).det = y - x ∧
    (!![1, x, x^2; 1, y, y^2; 1, z, z^2] : Matrix (Fin 3) (Fin 3) ℝ).det
      = (y - x) * (z - x) * (z - y) := by
  refine ⟨by simp [Matrix.det_fin_two_of], ?_⟩
  -- Expand the `3×3` determinant and factor: the diagonal-difference structure comes out.
  simp [Matrix.det_fin_three]; ring


theorem q6_invertible_iff_det : IsUnit (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  -- A square matrix is invertible iff its determinant is a unit; here `det = 1`.
  have hdet : (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    norm_num [Matrix.det_fin_two_of]
  rw [Matrix.isUnit_iff_isUnit_det, hdet]
  exact isUnit_one


theorem q7_det_row_scale :
    (!![2, 4; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det
      = 2 * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  norm_num [Matrix.det_fin_two_of]


open Equiv Equiv.Perm in
theorem q8_det_transpose {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) :
    Aᵀ.det = A.det := by
  -- In the permutation-sum `det = ∑_σ sign σ · ∏ᵢ A_{σ(i), i}`, reindex the sum by `σ ↦ σ⁻¹`:
  -- the sign is unchanged and the product just runs over the same factors in another order.
  rw [Matrix.det_apply', Matrix.det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  simp


theorem q9_det_inv (A B : Matrix (Fin 2) (Fin 2) ℝ) (h : A * B = 1) :
    A.det * B.det = 1 := by
  -- Determinant is multiplicative, so `det A · det B = det (A B) = det I = 1`.
  rw [← Matrix.det_mul, h, Matrix.det_one]


theorem q10_skew_odd_singular (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Aᵀ = -A) :
    A.det = 0 := by
  -- `det A = det Aᵀ = det (-A) = (-1)³ · det A = -det A`, so `2 · det A = 0`, hence `det A = 0`.
  have h1 : A.det = (-A).det := by rw [← h, Matrix.det_transpose]
  rw [Matrix.det_neg, Fintype.card_fin] at h1
  have h2 : (2 : ℝ) * A.det = 0 := by linear_combination h1
  linarith
