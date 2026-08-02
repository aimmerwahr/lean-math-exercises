import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.Eigenvalues

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem q1_eigen_iff_ker (f : Module.End K V) (l : K) (v : V) :
    f v = l • v ↔ v ∈ LinearMap.ker (f - l • 1) := by
  -- `(f - λ·id) v = f v - λ • v`, which is `0` exactly when `f v = λ • v`.
  simp [LinearMap.mem_ker, sub_eq_zero]

theorem q2_eigenvalue_iff_not_injective (f : Module.End K V) (l : K) :
    (∃ v : V, v ≠ 0 ∧ f v = l • v) ↔ ¬ Function.Injective ⇑(f - l • 1) := by
  -- Not injective means the kernel is nonzero, i.e. there is a nonzero eigenvector (q1).
  rw [← LinearMap.ker_eq_bot, ← ne_eq, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hfv⟩
    exact ⟨v, (q1_eigen_iff_ker f l v).mp hfv, hv⟩
  · rintro ⟨v, hmem, hv⟩
    exact ⟨v, hv, (q1_eigen_iff_ker f l v).mpr hmem⟩

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

theorem q4_eig_2x2 :
    Matrix.toLin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] = (3 : ℝ) • ![1, 1] ∧
    Matrix.toLin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ![1, -1] = (1 : ℝ) • ![1, -1] := by
  constructor <;>
    · ext i; fin_cases i <;>
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

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
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

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

theorem q7_diagonal_eigs :
    Matrix.toLin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] = (2 : ℝ) • ![1, 0] ∧
    Matrix.toLin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = (3 : ℝ) • ![0, 1] := by
  constructor <;>
    · ext i; fin_cases i <;>
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem q8_distinct_independent_concrete :
    LinearIndependent ℝ ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp [Fin.sum_univ_two] at h0 h1
  intro i; fin_cases i <;> simp <;> linarith

open scoped ComplexOrder in
theorem q9_hermitian_eigenvalue_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.conjTranspose = A) (l : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hAv : A.mulVec v = l • v) :
    star l = l := by
  -- Write `r = ⟪v, v⟫ = Σ|vᵢ|²`: real, and nonzero because `v ≠ 0`. And consider the "energy"
  -- `q = ⟪v, A v⟫`. On one hand `q = λ · r`. On the other, being Hermitian makes `q` equal to its
  -- own conjugate. So `λ · r = conj λ · r`, and cancelling `r ≠ 0` forces `conj λ = λ`.
  have hr_ne : star v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
  have hr_real : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
    rw [← Matrix.star_dotProduct_star, star_star]
  have hq : star v ⬝ᵥ A.mulVec v = l * (star v ⬝ᵥ v) := by
    rw [hAv, dotProduct_smul, smul_eq_mul]
  -- `q` is invariant under conjugation: conjugating swaps the two vectors and turns `A` into `Aᴴ`,
  -- which equals `A` again.
  have hq_real : star (star v ⬝ᵥ A.mulVec v) = star v ⬝ᵥ A.mulVec v := by
    rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hA,
      ← Matrix.dotProduct_mulVec]
  rw [hq, star_mul', hr_real] at hq_real
  have hzero : (star l - l) * (star v ⬝ᵥ v) = 0 := by rw [sub_mul, hq_real, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hr_ne)

theorem q10_nilpotent_only_zero (f : Module.End K V) (k : ℕ) (hk : f ^ k = 0)
    (l : K) (v : V) (hv : v ≠ 0) (hfv : f v = l • v) : l = 0 := by
  -- Applying `f` repeatedly to the eigenvector scales it by `λ` each time: `fᵐ v = λᵐ • v`.
  have hpow : ∀ m, (f ^ m) v = l ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Module.End.mul_apply, hfv, map_smul, ih, smul_smul, pow_succ']
  -- With `m = k` the left side is `0`, so `λᵏ • v = 0`; as `v ≠ 0`, `λᵏ = 0`, hence `λ = 0`.
  have hz : l ^ k • v = 0 := by rw [← hpow k, hk, LinearMap.zero_apply]
  have hlk : l ^ k = 0 := (smul_eq_zero.mp hz).resolve_right hv
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero] at hlk; exact absurd hlk one_ne_zero
  · exact (pow_eq_zero_iff hkpos.ne').mp hlk

theorem q11_poly_eigenvector (f : Module.End K V) (l c d : K) (v : V)
    (hfv : f v = l • v) :
    (f ^ 2 + c • f + d • 1 : Module.End K V) v = (l ^ 2 + c * l + d) • v := by
  -- Applying `f` twice scales by `λ²`.
  have hff : (f ^ 2) v = l ^ 2 • v := by
    rw [pow_two, Module.End.mul_apply, hfv, map_smul, hfv, smul_smul, ← pow_two]
  -- Expand the operator termwise; each summand becomes a scalar multiple of `v`, then collect.
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hff, hfv]
  rw [smul_smul, ← add_smul, ← add_smul]

end Solutions.LinearAlgebra.Eigenvalues
