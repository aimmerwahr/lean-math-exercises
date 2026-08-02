import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.Matrices

theorem q1_matmul_concrete :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![5, 6; 7, 8] = !![19, 22; 43, 50] := by
  norm_num [Matrix.mul_fin_two]

theorem q2_noncommute :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 1, 1]
      ≠ !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
  -- The two products differ already in the top-left entry (`2` versus `1`).
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [Matrix.mul_fin_two] at this

theorem q3_rotation_action :
    Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] = ![0, 1] ∧
    Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = ![-1, 0] := by
  -- Both are direct matrix-times-vector computations.
  constructor <;>
    · ext i; fin_cases i <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem q4_comp_eq_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.toLin' (A * B) = (Matrix.toLin' A).comp (Matrix.toLin' B) := by
  -- The whole content is that `(A * B) · v = A · (B · v)`: matrix multiplication is *defined* so
  -- that acting by a product is acting by the factors in turn.
  apply LinearMap.ext; intro v
  rw [Matrix.toLin'_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    Matrix.mulVec_mulVec]

theorem q5_one_sided_inverse (A B : Matrix (Fin 2) (Fin 2) ℝ) (hAB : A * B = 1) : B * A = 1 := by
  -- Pass to the associated maps. `A * B = 1` makes `toLin' B` have a left inverse, hence it is
  -- injective; in finite dimension injective forces surjective, so `toLin' B` is a bijection.
  -- Its left inverse `toLin' A` is then a genuine two-sided inverse, giving `B * A = 1`.
  have key : (Matrix.toLin' A).comp (Matrix.toLin' B) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hAB, Matrix.toLin'_one]
  have hL : Function.LeftInverse (Matrix.toLin' A) (Matrix.toLin' B) :=
    fun v => by have := LinearMap.congr_fun key v; simpa using this
  have hBsurj : Function.Surjective (Matrix.toLin' B) :=
    (LinearMap.injective_iff_surjective).mp hL.injective
  have hR : Function.RightInverse (Matrix.toLin' A) (Matrix.toLin' B) :=
    hL.rightInverse_of_surjective hBsurj
  have hBA : (Matrix.toLin' B).comp (Matrix.toLin' A) = LinearMap.id := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.comp_apply, LinearMap.id_apply]; exact hR v
  have hmap : Matrix.toLin' (B * A) = Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]; exact hBA
  exact Matrix.toLin'.injective hmap

theorem q6_inverse_concrete :
    (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, -1; -1, 2] = 1 := by
  rw [Matrix.one_fin_two]; norm_num [Matrix.mul_fin_two]

theorem q7_conjugation_concrete :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 0; 0, 3] * !![1, -1; 0, 1]
      = !![2, 1; 0, 3] := by
  norm_num [Matrix.mul_fin_two]

theorem q8_no_commutator_eq_one (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B - B * A ≠ 1 := by
  -- Take the trace of both sides. By cyclicity `tr (A B) = tr (B A)`, so the left side has trace
  -- `0`; but `tr I = 2`. The equation would force `0 = 2`.
  intro h
  have htr : Matrix.trace (A * B - B * A) = Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [h]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, Matrix.trace_one] at htr
  norm_num at htr

theorem q9_trace_conj_invariant (A P Q : Matrix (Fin 2) (Fin 2) ℝ) (h : Q * P = 1) :
    Matrix.trace (P * A * Q) = Matrix.trace A := by
  -- Cyclicity moves `Q` to the front: `tr (P A Q) = tr (Q P A) = tr (1 · A) = tr A`.
  rw [Matrix.trace_mul_comm, ← mul_assoc, h, one_mul]

end Solutions.LinearAlgebra.Matrices
