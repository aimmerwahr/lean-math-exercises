import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.Eigenvalues

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Eigenvectors are the kernel elements of `f - λ·id`. -/
theorem q1_eigen_iff_ker (f : Module.End K V) (l : K) (v : V) :
    f v = l • v ↔ v ∈ LinearMap.ker (f - l • 1) := by
  -- `(f - λ·id) v = f v - λ • v`, which is `0` exactly when `f v = λ • v`.
  simp [LinearMap.mem_ker, sub_eq_zero]

/-- `λ` is an eigenvalue iff `f - λ·id` is not injective. -/
theorem q2_eigenvalue_iff_not_injective (f : Module.End K V) (l : K) :
    (∃ v : V, v ≠ 0 ∧ f v = l • v) ↔ ¬ Function.Injective ⇑(f - l • 1) := by
  -- Not injective means the kernel is nonzero, i.e. there is a nonzero eigenvector (q1).
  rw [← LinearMap.ker_eq_bot, ← ne_eq, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hfv⟩
    exact ⟨v, (q1_eigen_iff_ker f l v).mp hfv, hv⟩
  · rintro ⟨v, hmem, hv⟩
    exact ⟨v, hv, (q1_eigen_iff_ker f l v).mpr hmem⟩

/-- Eigenvectors for distinct eigenvalues are linearly independent. -/
theorem q3_distinct_independent (f : Module.End K V) (l₁ l₂ : K) (v₁ v₂ : V)
    (h₁ : f v₁ = l₁ • v₁) (h₂ : f v₂ = l₂ • v₂)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hl : l₁ ≠ l₂) :
    LinearIndependent K ![v₁, v₂] := by
  -- Suppose `s • v₁ + t • v₂ = 0`. Applying `f` gives `(s λ₁) • v₁ + (t λ₂) • v₂ = 0`, while
  -- multiplying the relation by `λ₁` gives `(s λ₁) • v₁ + (t λ₁) • v₂ = 0`. Subtracting isolates
  -- `t (λ₂ - λ₁) • v₂ = 0`; as `v₂ ≠ 0` and `λ₁ ≠ λ₂`, this forces `t = 0`, then `s = 0`.
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hf : (s * l₁) • v₁ + (t * l₂) • v₂ = 0 := by
    have := congrArg f hst; simpa [h₁, h₂, map_add, map_smul, smul_smul] using this
  have hl₁ : (s * l₁) • v₁ + (t * l₁) • v₂ = 0 := by
    have := congrArg (l₁ • ·) hst
    simp only [smul_add, smul_zero, smul_smul] at this
    rw [mul_comm l₁ s, mul_comm l₁ t] at this; exact this
  have hne : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
  have ht0 : t = 0 := by
    have e : (t * l₂) • v₂ = (t * l₁) • v₂ := add_left_cancel (hf.trans hl₁.symm)
    have hz : (t * l₂ - t * l₁) • v₂ = 0 := by rw [sub_smul, e, sub_self]
    rcases smul_eq_zero.mp hz with hc | hc
    · rw [← mul_sub] at hc; exact (mul_eq_zero.mp hc).resolve_right hne
    · exact absurd hc hv₂
  have hs0 : s = 0 := by
    rw [ht0, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right hv₁
  exact ⟨hs0, ht0⟩

/-- Eigenvalues and eigenvectors of `!![2,1;1,2]`. -/
theorem q4_eig_2x2 :
    Matrix.toLin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] = (3 : ℝ) • ![1, 1] ∧
    Matrix.toLin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ![1, -1] = (1 : ℝ) • ![1, -1] := by
  constructor <;>
    · ext i; fin_cases i <;>
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- The rotation has no real eigenvalue, but eigenvalue `i` over `ℂ`. -/
theorem q5_rotation_field_dependence :
    (¬ ∃ (μ : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧
      Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = μ • v) ∧
    Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ![Complex.I, 1]
      = Complex.I • ![Complex.I, 1] := by
  constructor
  · -- Over `ℝ`: if `A v = μ v` with `v = (a,b)`, then `-b = μ a` and `a = μ b`, so
    -- `(μ² + 1) b = 0`; since `μ² + 1 > 0`, `b = 0`, then `a = 0`, contradicting `v ≠ 0`.
    rintro ⟨μ, v, hv, hEq⟩
    have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have key : (μ ^ 2 + 1) * v 1 = 0 := by linear_combination (-1) * h0 + (-μ) * h1
    have hv1 : v 1 = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h (by positivity)
      · exact h
    have hv0 : v 0 = 0 := by rw [h1, hv1, mul_zero]
    exact hv (by funext i; fin_cases i <;> simp [hv0, hv1])
  · -- Over `ℂ`: `A · (i, 1) = (-1, i) = i · (i, 1)` since `i² = -1`.
    ext i; fin_cases i <;>
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff]

/-- The shear's eigenvectors for eigenvalue `1` are exactly the `x`-axis. -/
theorem q6_shear_eigenspace (v : Fin 2 → ℝ) :
    Matrix.toLin' (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) v = v ↔ v 1 = 0 := by
  -- `A v = v` unfolds to `(v₀ + v₁, v₁) = (v₀, v₁)`, whose first coordinate says `v₁ = 0`.
  constructor
  · intro hEq
    have h0 := congrFun hEq 0
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    linarith
  · intro hv1
    funext i; fin_cases i <;>
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv1]

/-- Diagonal matrix: eigenvalues are the diagonal entries. -/
theorem q7_diagonal_eigs :
    Matrix.toLin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] = (2 : ℝ) • ![1, 0] ∧
    Matrix.toLin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = (3 : ℝ) • ![0, 1] := by
  constructor <;>
    · ext i; fin_cases i <;>
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- The two eigenvectors are linearly independent. -/
theorem q8_distinct_independent_concrete :
    LinearIndependent ℝ ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp [Fin.sum_univ_two] at h0 h1
  intro i; fin_cases i <;> simp <;> linarith

end Solutions.LinearAlgebra.Eigenvalues
