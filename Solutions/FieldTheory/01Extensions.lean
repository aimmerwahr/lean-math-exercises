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


theorem q2_one_i_linear_independent (a b : ℝ) :
    (a : ℂ) + b * Complex.I = 0 → a = 0 ∧ b = 0 := by
  intro hzero
  constructor
  · simpa using congrArg Complex.re hzero
  · simpa using congrArg Complex.im hzero


theorem q3_one_i_spans_complex :
    Submodule.span ℝ ({(1 : ℂ), Complex.I} : Set ℂ) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  rw [← Complex.re_add_im z]
  apply (Submodule.span ℝ ({(1 : ℂ), Complex.I} : Set ℂ)).add_mem
  · rw [show (z.re : ℂ) = z.re • (1 : ℂ) by simp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [show z.im * Complex.I = z.im • Complex.I by simp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))


theorem q4_degree_complex_real : Module.finrank ℝ ℂ = 2 := by
  let e : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • Complex.I
      left_inv := fun z => by simp
      right_inv := fun c => by
        funext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }
  let b : Module.Basis (Fin 2) ℝ ℂ := Module.Basis.ofEquivFun e
  rw [Module.finrank_eq_card_basis b]
  norm_num


theorem q5_i_root :
    (Polynomial.X ^ 2 + Polynomial.C 1 : ℝ[X]).eval₂ (algebraMap ℝ ℂ) Complex.I = 0 := by
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Complex.I_sq]
  norm_num


theorem q6_i_integral : IsIntegral ℝ Complex.I := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C 1, Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simpa only [Polynomial.aeval_def] using q5_i_root


theorem q7_complex_quadratic_relation (z : ℂ) :
    z ^ 2 - ((2 * z.re : ℝ) : ℂ) * z + ((Complex.normSq z : ℝ) : ℂ) = 0 := by
  apply Complex.ext <;>
    simp [pow_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring


theorem q8_every_complex_integral (z : ℂ) : IsIntegral ℝ z := by
  let p : ℝ[X] := Polynomial.X ^ 2 +
    (Polynomial.C (-2 * z.re) * Polynomial.X + Polynomial.C (Complex.normSq z))
  refine ⟨p, ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply lt_of_le_of_lt
      (max_le
        (le_trans (Polynomial.degree_mul_le _ _)
          (show (Polynomial.C (-2 * z.re)).degree + Polynomial.X.degree ≤ (0 : WithBot ℕ) + 1 by
            exact add_le_add Polynomial.degree_C_le (by simp)))
        (le_trans Polynomial.degree_C_le (by simp)))
    norm_num
  · simp only [p, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [show (algebraMap ℝ ℂ) (-2 * z.re) = -((2 * z.re : ℝ) : ℂ) by norm_num]
    simpa [sub_eq_add_neg, add_assoc] using q7_complex_quadratic_relation z


theorem q9_complex_is_generated_by_i :
    IntermediateField.adjoin ℝ ({Complex.I} : Set ℂ) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  rw [← Complex.re_add_im z]
  apply (IntermediateField.adjoin ℝ ({Complex.I} : Set ℂ)).add_mem
  · exact IntermediateField.adjoin.algebraMap_mem ℝ _ z.re
  · rw [show z.im * Complex.I = z.im • Complex.I by simp]
    exact (IntermediateField.adjoin ℝ ({Complex.I} : Set ℂ)).smul_mem
      (IntermediateField.mem_adjoin_simple_self ℝ Complex.I)


theorem q10_quadratic_extension_has_no_proper_intermediate_field (F : IntermediateField ℝ ℂ) :
    F = ⊥ ∨ F = ⊤ := by
  have hdegree := q4_degree_complex_real
  have hmul := Module.finrank_mul_finrank ℝ F ℂ
  rw [hdegree] at hmul
  have hF : Module.finrank ℝ F = 1 ∨ Module.finrank ℝ F = 2 := by
    have hdvd : Module.finrank ℝ F ∣ 2 := ⟨Module.finrank F ℂ, hmul.symm⟩
    exact (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd
  rcases hF with hF | hF
  · exact Or.inl (IntermediateField.finrank_eq_one_iff.mp hF)
  · right
    have htop : Module.finrank F ℂ = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
      simpa [hF] using hmul
    exact IntermediateField.finrank_eq_one_iff_eq_top.mp htop


theorem q11_root_of_linear_polynomial (K : Type*) [Field K] (a : K) :
    (Polynomial.X - Polynomial.C a).eval a = 0 := by
  simp


theorem q12_indeterminate_transcendental (K : Type*) [Field K] :
    Transcendental K (Polynomial.X : K[X]) := by
  rw [transcendental_iff]
  intro p hp
  simpa [Polynomial.aeval_def] using hp

end Solutions.FieldTheory.Extensions
