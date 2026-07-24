import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Determinants

The **determinant** of a square matrix is a single scalar that is multilinear and alternating in
the rows and normalized (`det 1 = 1`) — properties that pin it down uniquely. Its two headline
features are **multiplicativity** `det (A B) = det A · det B` and the **singularity test**
`A` invertible ↔ `det A ≠ 0`. It is at once an algebraic gadget (a signed sum over permutations,
whence `det Aᵀ = det A`) and a geometric one (signed volume scaling), detecting invertibility in
one number.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/Determinants.lean`. Do **not** commit your proofs into this file.

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

end

/-- **Question 1.**

Compute the determinant of `!![1,2;3,4]`. -/
theorem q1_det_2x2 : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det = -2 := by
  sorry

/-- **Question 2.**

Compute the determinant of `!![2,0,1;1,3,2;0,1,1]`. -/
theorem q2_det_3x3 :
    (!![2, 0, 1; 1, 3, 2; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = 3 := by
  sorry

/-- **Question 3.**

Verify `det (A B) = det A · det B` for `A = !![1,2;3,4]`, `B = !![5,6;7,8]` — by computing both
sides, not by invoking multiplicativity.

Prove without using `Matrix.det_mul`. -/
theorem q3_det_mul_concrete :
    ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![5, 6; 7, 8]).det
      = (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det * (!![5, 6; 7, 8]).det := by
  sorry

/-- **Question 4.**

The determinant of a triangular matrix is the product of its diagonal, and a shear has
determinant `1`: `det !![2,5;0,3] = 2 * 3` and `det !![1,7;0,1] = 1`. -/
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

Decide invertibility from the determinant: `!![2,1;1,1]` is invertible (its determinant is
nonzero). -/
theorem q6_invertible_iff_det : IsUnit (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  sorry

/-- **Question 7.**

Scaling one row by `2` scales the determinant by `2`:
`det !![2,4;3,4] = 2 * det !![1,2;3,4]`. -/
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

end Exercises.LinearAlgebra.Determinants
