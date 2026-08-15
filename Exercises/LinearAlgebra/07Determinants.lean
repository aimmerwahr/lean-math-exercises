import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Determinants

The **determinant** is the unique normalized alternating multilinear measurement of the rows of a
square matrix. This sheet follows that structure: first understand the effect of row operations,
then derive transpose, multiplicativity, and the singularity test. Symbolic examples (Vandermonde
and skew-symmetric matrices) are applications of those principles, not isolated arithmetic drills.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/07Determinants.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project.
-/
namespace Exercises.LinearAlgebra.Determinants

open Matrix

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Closed forms for `2×2` and `3×3` determinants, and expanding a `2×2` product / the identity.
#check @Matrix.det_fin_two_of
#check @Matrix.det_fin_three
#check @Matrix.mul_fin_two
#check @Matrix.one_fin_two

-- Invertibility via the determinant.
#check @Matrix.isUnit_iff_isUnit_det

-- The permutation-sum definition of the determinant, and reindexing tools for `q8`.
#check @Matrix.det_apply'
#check @Equiv.Perm.sign_inv

-- The determinant of a negated matrix picks up `(-1)` per row.
#check @Matrix.det_neg

end

/-- **Question 1.**

Use the signed-sum definition once to establish the `2 × 2` determinant formula. This is the only
purely computational warm-up; later questions use it as evidence for general principles. -/
theorem q1_det_2x2 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det = -2 := by
  sorry


/-- **Question 2.**

Scaling a row scales the determinant by the same scalar. Verify the principle in a small case, then
identify the corresponding general determinant lemma. -/
theorem q2_det_3x3 :
    (!![2, 0, 1; 1, 3, 2; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = 3 := by
  sorry


/-- **Question 3.**

Adding a multiple of one row to another leaves the determinant unchanged. Use this row operation to
explain why a shear has determinant `1`. -/
theorem q3_det_mul_concrete :
    ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![5, 6; 7, 8]).det
      = (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det * (!![5, 6; 7, 8]).det := by
  sorry


/-- **Question 4.**

Use triangularity and the preceding row-operation principle to compute determinants structurally,
rather than entry-by-entry. -/
theorem q4_det_triangular :
    (!![2, 5; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 2 * 3 ∧
    (!![1, 7; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  sorry


/-- **Question 5.**

The `2×2` and `3×3` Vandermonde determinants factor as products of node differences:
`det !![1,x;1,y] = y - x` and `det !![1,x,x^2;1,y,y^2;1,z,z^2] = (y - x) * (z - x) * (z - y)`. -/
theorem q5_vandermonde (x y z : ℝ) :
    (!![1, x; 1, y] : Matrix (Fin 2) (Fin 2) ℝ).det = y - x ∧
    (!![1, x, x^2; 1, y, y^2; 1, z, z^2] : Matrix (Fin 3) (Fin 3) ℝ).det
      = (y - x) * (z - x) * (z - y) := by
  sorry


/-- **Question 6.**

Use the determinant criterion to decide invertibility of a concrete matrix. -/
theorem q6_invertible_iff_det : IsUnit (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  sorry


/-- **Question 7.**

Relate row scaling to signed area: compare a matrix with the result of scaling one of its rows. -/
theorem q7_det_row_scale :
    (!![2, 4; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det
      = 2 * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  sorry


/-- **Question 8.**

A matrix and its transpose have the same determinant: `det Aᵀ = det A`. (Work from the
permutation-sum definition, reindexing the sum by `σ ↦ σ⁻¹`.)

Prove without using `Matrix.det_transpose`. -/
theorem q8_det_transpose {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) :
    Aᵀ.det = A.det := by
  sorry


/-- **Question 9.**

The determinant of an inverse is the reciprocal: if `A B = I`, then `det A · det B = 1`. -/
theorem q9_det_inv (A B : Matrix (Fin 2) (Fin 2) ℝ) (h : A * B = 1) :
    A.det * B.det = 1 := by
  sorry


/-- **Question 10.**

A matrix is **skew-symmetric** when `Aᵀ = -A`. Show that a skew-symmetric matrix of **odd** size is
singular: for `A : ℝ³ˣ³` with `Aᵀ = -A`, `det A = 0`.

Use Question 8 for transpose invariance; do not use `Matrix.det_transpose` directly. -/
theorem q10_skew_odd_singular (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Aᵀ = -A) :
    A.det = 0 := by
  sorry

end Exercises.LinearAlgebra.Determinants
