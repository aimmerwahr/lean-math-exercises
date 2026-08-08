import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Tactic

namespace Solutions.FieldTheory.Extensions

open scoped IntermediateField Polynomial

theorem q1_complex_coordinates (z : ℂ) :
    ∃! ab : ℝ × ℝ, z = (ab.1 : ℂ) + ab.2 * Complex.I := by
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · -- The real and imaginary parts reconstruct a complex number.
    apply Complex.ext <;> simp
  · intro ab hab
    apply Prod.ext
    · -- Taking real parts recovers the first coordinate.
      simpa using (congrArg Complex.re hab).symm
    · -- Taking imaginary parts recovers the second coordinate.
      simpa using (congrArg Complex.im hab).symm


theorem q2_adjoin_degree {K L : Type*} [Field K] [Field L] [Algebra K L]
    (a : L) (ha : IsIntegral K a) :
    Module.finrank K K⟮a⟯ = (minpoly K a).natDegree := by
  exact IntermediateField.adjoin.finrank ha


theorem q3_tower_law {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [FiniteDimensional K F] [FiniteDimensional F L] :
    Module.finrank K F * Module.finrank F L = Module.finrank K L := by
  exact Module.finrank_mul_finrank K F L


theorem q4_finite_implies_algebraic {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L) : IsAlgebraic K a := by
  exact IsAlgebraic.of_finite K a


theorem q5_minpoly_base (K : Type*) [Field K] (a : K) :
    minpoly K a = Polynomial.X - Polynomial.C a := by
  simpa using (minpoly.eq_X_sub_C K a)


theorem q6_intermediate_degree_dvd {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (F : IntermediateField K L) :
    Module.finrank K F ∣ Module.finrank K L := by
  simpa using IntermediateField.finrank_dvd_of_le_right (show F ≤ (⊤ : IntermediateField K L) from le_top)


theorem q7_sqrt2_irrational : Irrational (Real.sqrt 2) := by exact irrational_sqrt_two


theorem q8_base_generated_by_one (K : Type*) [Field K] :
    Submodule.span K ({(1 : K)} : Set K) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  -- Every scalar is its own scalar multiple of the vector `1`.
  rw [show x = x • (1 : K) by simp]
  exact Submodule.smul_mem _ x (Submodule.subset_span (by simp))


theorem q9_transcendental_X (K : Type*) [Field K] :
    Transcendental K (Polynomial.X : K[X]) := by
  exact Polynomial.transcendental_X K

end Solutions.FieldTheory.Extensions
