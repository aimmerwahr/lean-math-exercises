import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.Basis

open Module

variable {K : Type*} [Field K] {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n : ℕ} (b : Basis (Fin n) K V)

theorem q1_coords_unique (c d : Fin n → K)
    (h : ∑ i, c i • b i = ∑ i, d i • b i) : c = d := by
  -- Linear independence says: a combination of the basis vectors that equals `0` has every
  -- coefficient `0`. So rewrite the hypothesis as a single vanishing combination.
  have hli := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have hzero : ∑ i, (c i - d i) • b i = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, h, sub_self]
  -- Independence forces each `c i - d i = 0`, i.e. `c i = d i`.
  funext i
  exact sub_eq_zero.mp (hli (fun i => c i - d i) hzero i)


theorem q2_map_determined (f g : V →ₗ[K] W) (h : ∀ i, f (b i) = g (b i)) : f = g := by
  -- Two maps that agree on a basis agree everywhere: expand an arbitrary `x` in the basis,
  -- then push each map through the sum and the scalars, where the values agree termwise.
  ext x
  conv_lhs => rw [← b.sum_repr x]
  conv_rhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, h]


theorem q3_prescribe_map (w : Fin n → W) : ∃ f : V →ₗ[K] W, ∀ i, f (b i) = w i :=
  -- The map "extend `w` linearly off the basis" does the job, taking the prescribed value on
  -- each basis vector.
  ⟨b.constr K w, fun i => b.constr_basis K w i⟩


theorem q4_isBasis_concrete :
    ∃ B : Basis (Fin 2) ℝ (Fin 2 → ℝ), ⇑B = ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
  -- The two vectors are independent (a vanishing combination forces both coefficients to `0`),
  -- and two independent vectors in a `2`-dimensional space always form a basis.
  have hli : LinearIndependent ℝ ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [Fin.sum_univ_two] at h0 h1
    intro i; fin_cases i <;> simp <;> linarith
  have hcard : Fintype.card (Fin 2) = finrank ℝ (Fin 2 → ℝ) := by simp
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩


theorem q5_extend_concrete :
    ∃ B : Basis (Fin 2) ℝ (Fin 2 → ℝ), B 0 = ![1, 2] := by
  -- Complete `(1,2)` with `(0,1)`. The two vectors are independent, so they form a basis of
  -- `ℝ²`; the first vector is the given one.
  have hli : LinearIndependent ℝ ![(![1, 2] : Fin 2 → ℝ), ![0, 1]] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [Fin.sum_univ_two] at h0 h1
    intro i; fin_cases i <;> simp_all
  have hcard : Fintype.card (Fin 2) = finrank ℝ (Fin 2 → ℝ) := by simp
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank hli hcard]; rfl


theorem q6_too_many_dependent (v : Fin 3 → (Fin 2 → ℝ)) : ¬ LinearIndependent ℝ v := by
  -- Independence would give `3` independent vectors in a `2`-dimensional space, but an
  -- independent family has at most `dim = 2` vectors.
  intro h
  have := h.fintype_card_le_finrank
  simp at this


theorem q7_too_few_dont_span : ¬ ∃ v : Fin 2 → ℝ, Submodule.span ℝ {v} = ⊤ := by
  -- The span of one vector has dimension at most `1`, whereas `ℝ²` has dimension `2`.
  rintro ⟨v, hv⟩
  have h1 := finrank_span_le_card (R := ℝ) ({v} : Set (Fin 2 → ℝ))
  rw [hv] at h1
  simp [finrank_top] at h1


theorem q8_indep_image_injective (f : V →ₗ[K] W)
    (hf : LinearIndependent K fun i => f (b i)) : Function.Injective f := by
  -- It suffices that `ker f = 0`. Take `z` with `f z = 0` and expand it in the basis:
  -- `0 = f z = ∑ᵢ (repr z)ᵢ • f(bᵢ)`. Independence of the images forces every coordinate to
  -- vanish, so `z = 0`.
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have key : ∑ i, b.repr z i • f (b i) = 0 := by
    have hsum : ∑ i, b.repr z i • f (b i) = f (∑ i, b.repr z i • b i) := by
      rw [map_sum]; simp only [map_smul]
    rw [hsum, b.sum_repr, hz]
  have hcoef : ∀ i, b.repr z i = 0 := Fintype.linearIndependent_iff.mp hf _ key
  have hzero : b.repr z = 0 := by ext i; exact hcoef i
  exact b.repr.map_eq_zero_iff.mp hzero

end Solutions.LinearAlgebra.Basis
