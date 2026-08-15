import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.SpanIndependence

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


theorem q1_mem_span_explicit : (![2, 5] : Fin 2 → ℝ) ∈
    Submodule.span ℝ {(![1, 0] : Fin 2 → ℝ), ![0, 1]} := by
  -- Write the target vector as a linear combination of the two coordinate vectors.
  have hcomb : (![2, 5] : Fin 2 → ℝ) =
      (2 : ℝ) • (![1, 0] : Fin 2 → ℝ) + (5 : ℝ) • ![0, 1] := by
    funext i
    fin_cases i <;> norm_num
  rw [hcomb]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)


theorem q2_span_universal (s : Set V) (W : Submodule K V) :
    Submodule.span K s ≤ W ↔ s ⊆ (W : Set V) := by
  constructor
  · intro h x hx
    exact h (Submodule.subset_span hx)
  · intro h x hx
    -- Membership in a span is built from its generators by the vector-space operations.
    induction hx using Submodule.span_induction with
    | mem x hx => exact h hx
    | zero => exact W.zero_mem
    | add x y _ _ hx hy => exact W.add_mem hx hy
    | smul a x _ hx => exact W.smul_mem a hx


theorem q3_span_mono {s t : Set V} (h : s ⊆ t) :
    Submodule.span K s ≤ Submodule.span K t := by
  -- Every generator of `s` belongs to the span of `t`, so the universal property applies.
  exact q2_span_universal s (Submodule.span K t) |>.mpr fun x hx =>
    Submodule.subset_span (h hx)


theorem q4_span_idempotent (W : Submodule K V) : Submodule.span K (W : Set V) = W := by
  apply le_antisymm
  · exact q2_span_universal _ W |>.mpr fun _ hx => hx
  · exact Submodule.subset_span


theorem q5_single_nonzero {ι : Type*} (i : ι) : Finsupp.single i (1 : K) ≠ 0 :=
  Finsupp.single_ne_zero.mpr one_ne_zero


theorem q6_zero_dependent {ι : Type*} (v : ι → V) (i : ι) (hvi : v i = 0) :
    ¬ LinearIndependent K v := by
  intro hli
  -- The coefficient function concentrated at `i` is nonzero but gives the zero combination.
  have hcomb : Finsupp.linearCombination K v (Finsupp.single i (1 : K)) = 0 := by
    simp [hvi]
  have hzero := linearIndependent_iff.mp hli _ hcomb
  exact q5_single_nonzero i hzero


theorem q7_dependent_mem_span {n : ℕ} (v : Fin (n + 1) → V) :
    ¬ LinearIndependent K v ↔ ∃ i, v i ∈ Submodule.span K (v '' {j | j ≠ i}) := by
  constructor
  · intro h
    rw [linearIndependent_iff_eq_zero_of_smul_mem_span] at h
    push Not at h
    obtain ⟨i, a, ha, hane⟩ := h
    refine ⟨i, ?_⟩
    -- Divide a nontrivial relation by the nonzero coefficient of its chosen vector.
    have hrewrite : v i = a⁻¹ • (a • v i) := by
      rw [← mul_smul, inv_mul_cancel₀ hane, one_smul]
    rw [hrewrite]
    apply Submodule.smul_mem
    have hset : {j | j ≠ i} = Set.univ \ {i} := by ext; simp
    rw [hset]
    exact ha
  · rintro ⟨i, hi⟩ hli
    -- The coefficient `1` cannot multiply a member of an independent family into the others' span.
    have hzero := linearIndependent_iff_eq_zero_of_smul_mem_span.mp hli i 1 (by
      have hset : {j | j ≠ i} = Set.univ \ {i} := by ext; simp
      simpa [hset] using hi)
    exact one_ne_zero hzero


theorem q8_polynomial_coeff_zero {n : ℕ} (c : Fin (n + 1) → K)
    (hc : ∑ j, c j • (Polynomial.X : Polynomial K) ^ j.val = 0) (i : Fin (n + 1)) : c i = 0 := by
  -- The coefficient of `X^i` in the vanishing combination is exactly `c i`.
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff i.val) hc
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, Polynomial.coeff_X_pow] at hcoeff
  rw [Finset.sum_eq_single i] at hcoeff
  · simpa using hcoeff
  · intro j _ hji
    have hij : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    simp [hij]
  · simp


theorem q9_polynomials_independent {n : ℕ} : LinearIndependent K
    (fun i : Fin (n + 1) => (Polynomial.X : Polynomial K) ^ i.val) := by
  rw [Fintype.linearIndependent_iff]
  exact q8_polynomial_coeff_zero

end Solutions.LinearAlgebra.SpanIndependence
