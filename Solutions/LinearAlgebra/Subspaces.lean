import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Solutions.LinearAlgebra.Subspaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A vector lies in `U ⊔ W` iff it is a sum `u + w` with `u ∈ U`, `w ∈ W`. -/
theorem q1_mem_sup_iff (U W : Submodule K V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ u ∈ U, ∃ w ∈ W, u + w = x := by
  constructor
  · -- Forward direction. The set `S` of all sums `u + w` is itself a subspace containing
    -- both `U` and `W`, hence `U ⊔ W ≤ S` (as `U ⊔ W` is the *least* such). So `x ∈ S`.
    intro hx
    let S : Submodule K V :=
      { carrier := {y | ∃ u ∈ U, ∃ w ∈ W, u + w = y}
        zero_mem' := ⟨0, U.zero_mem, 0, W.zero_mem, by simp⟩
        add_mem' := by
          rintro a b ⟨u₁, hu₁, w₁, hw₁, rfl⟩ ⟨u₂, hu₂, w₂, hw₂, rfl⟩
          exact ⟨u₁ + u₂, U.add_mem hu₁ hu₂, w₁ + w₂, W.add_mem hw₁ hw₂, by abel⟩
        smul_mem' := by
          rintro c a ⟨u, hu, w, hw, rfl⟩
          exact ⟨c • u, U.smul_mem c hu, c • w, W.smul_mem c hw, by rw [smul_add]⟩ }
    have hUS : U ⊔ W ≤ S := by
      apply sup_le
      · intro u hu; exact ⟨u, hu, 0, W.zero_mem, by simp⟩
      · intro w hw; exact ⟨0, U.zero_mem, w, hw, by simp⟩
    exact hUS hx
  · -- Backward direction: `u ∈ U ≤ U ⊔ W` and `w ∈ W ≤ U ⊔ W`, and subspaces are closed
    -- under addition.
    rintro ⟨u, hu, w, hw, rfl⟩
    exact add_mem (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hw)

/-- `U ⊔ W ≤ X` iff both `U ≤ X` and `W ≤ X` (the sum is the least upper bound). -/
theorem q2_sup_le_iff (U W X : Submodule K V) :
    U ⊔ W ≤ X ↔ U ≤ X ∧ W ≤ X := by
  constructor
  · -- If the sum sits inside `X`, so do the summands, since `U, W ≤ U ⊔ W`.
    intro h
    exact ⟨le_sup_left.trans h, le_sup_right.trans h⟩
  · -- Conversely, take any `x ∈ U ⊔ W`, write it as `u + w` (q1), and land in `X`.
    rintro ⟨hU, hW⟩ x hx
    rw [q1_mem_sup_iff] at hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    exact add_mem (hU hu) (hW hw)

/-- `U ⊔ W = W` iff `U ≤ W`. -/
theorem q3_sup_eq_right_iff_le (U W : Submodule K V) :
    U ⊔ W = W ↔ U ≤ W := by
  constructor
  · -- `U ≤ U ⊔ W = W`.
    intro h
    calc U ≤ U ⊔ W := le_sup_left
      _ = W := h
  · -- Antisymmetry: `U ⊔ W ≤ W` (by q2, since `U ≤ W` and `W ≤ W`) and `W ≤ U ⊔ W`.
    intro h
    exact le_antisymm ((q2_sup_le_iff U W W).mpr ⟨h, le_rfl⟩) le_sup_right

/-- If `u ∈ U \ W` and `w ∈ W \ U`, then `u + w ∉ ↑U ∪ ↑W`. -/
theorem q4_add_notMem_union (U W : Submodule K V) {u w : V}
    (hu : u ∈ U) (hw : w ∈ W) (huW : u ∉ W) (hwU : w ∉ U) :
    u + w ∉ (↑U ∪ ↑W : Set V) := by
  -- Suppose the sum lands in one of the pieces and derive a contradiction.
  rintro (h | h)
  · -- If `u + w ∈ U`, then `w = (u + w) - u ∈ U`, contradicting `w ∉ U`.
    apply hwU
    have : w = (u + w) - u := by abel
    rw [this]
    exact U.sub_mem h hu
  · -- If `u + w ∈ W`, then `u = (u + w) - w ∈ W`, contradicting `u ∉ W`.
    apply huW
    have : u = (u + w) - w := by abel
    rw [this]
    exact W.sub_mem h hw

/-- The union `↑U ∪ ↑W` is a subspace (i.e. equals `↑(U ⊔ W)`) iff `U ≤ W` or `W ≤ U`. -/
theorem q5_union_isSubspace_iff_le (U W : Submodule K V) :
    (↑U ∪ ↑W : Set V) = ↑(U ⊔ W) ↔ U ≤ W ∨ W ≤ U := by
  constructor
  · -- Forward. If the pieces were incomparable we could pick `u ∈ U \ W` and `w ∈ W \ U`;
    -- then `u + w ∈ U ⊔ W = ↑U ∪ ↑W`, contradicting q4.
    intro h
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hUW, hWU⟩ := hcon
    rw [SetLike.not_le_iff_exists] at hUW hWU
    obtain ⟨u, hu, huW⟩ := hUW
    obtain ⟨w, hw, hwU⟩ := hWU
    have hmem : u + w ∈ U ⊔ W :=
      add_mem (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hw)
    -- pass to set membership so `h` can rewrite `↑(U ⊔ W)` back to `↑U ∪ ↑W`
    rw [← SetLike.mem_coe, ← h] at hmem
    exact q4_add_notMem_union U W hu hw huW hwU hmem
  · -- Backward. If say `U ≤ W`, then `U ⊔ W = W` (q3) and `↑U ∪ ↑W = ↑W`.
    rintro (h | h)
    · have hsup : U ⊔ W = W := (q3_sup_eq_right_iff_le U W).mpr h
      rw [hsup, Set.union_eq_right]
      exact fun x hx => h hx
    · have hsup : U ⊔ W = U := by
        rw [sup_comm]; exact (q3_sup_eq_right_iff_le W U).mpr h
      rw [hsup, Set.union_eq_left]
      exact fun x hx => h hx

/-- `Disjoint U W` iff the only common vector is `0`. -/
theorem q6_disjoint_iff_forall_eq_zero (U W : Submodule K V) :
    Disjoint U W ↔ ∀ x, x ∈ U → x ∈ W → x = 0 := by
  -- Disjointness of subspaces means they meet only in the zero subspace `⊥ = {0}`; so a
  -- vector lying in both must be `0`, and conversely.
  rw [disjoint_iff_inf_le]
  constructor
  · intro h x hxU hxW
    have hx : x ∈ U ⊓ W := Submodule.mem_inf.mpr ⟨hxU, hxW⟩
    have : x ∈ (⊥ : Submodule K V) := h hx
    rwa [Submodule.mem_bot] at this
  · intro h x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_bot]
    exact h x hx.1 hx.2

/-- The sum is direct iff decompositions `u + w` are unique. -/
theorem q7_directSum_iff_unique_decomp (U W : Submodule K V) :
    Disjoint U W ↔
      ∀ u₁ ∈ U, ∀ u₂ ∈ U, ∀ w₁ ∈ W, ∀ w₂ ∈ W,
        u₁ + w₁ = u₂ + w₂ → u₁ = u₂ ∧ w₁ = w₂ := by
  rw [q6_disjoint_iff_forall_eq_zero]
  constructor
  · -- Forward. From `u₁ + w₁ = u₂ + w₂`, the vector `u₁ - u₂ = w₂ - w₁` lies in both `U`
    -- and `W`, hence is `0`; so `u₁ = u₂`, and cancelling gives `w₁ = w₂`.
    intro h u₁ hu₁ u₂ hu₂ w₁ hw₁ w₂ hw₂ heq
    have hkey : u₁ - u₂ = w₂ - w₁ := by
      rw [sub_eq_sub_iff_add_eq_add, heq]; exact add_comm _ _
    have hdU : u₁ - u₂ ∈ U := U.sub_mem hu₁ hu₂
    have hdW : u₁ - u₂ ∈ W := by rw [hkey]; exact W.sub_mem hw₂ hw₁
    have hd : u₁ - u₂ = 0 := h _ hdU hdW
    have hu_eq : u₁ = u₂ := sub_eq_zero.mp hd
    subst hu_eq
    exact ⟨rfl, add_left_cancel heq⟩
  · -- Backward. For `x ∈ U ⊓ W`, the two decompositions `x + 0` and `0 + x` of `x` must
    -- agree, forcing `x = 0`.
    intro h x hxU hxW
    have := h x hxU 0 U.zero_mem 0 W.zero_mem x hxW (by simp)
    exact this.1

/-- Modular law: `U ≤ W → U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W`. -/
theorem q8_modular_law (U W X : Submodule K V) (h : U ≤ W) :
    U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W := by
  apply le_antisymm
  · -- `≤` holds in any lattice: bound each summand.
    apply sup_le
    · exact le_inf le_sup_left h
    · exact le_inf (inf_le_left.trans le_sup_right) inf_le_right
  · -- `≥` is the modular content. Take `x ∈ (U ⊔ X) ⊓ W`, write `x = u + y` with `u ∈ U`,
    -- `y ∈ X` (q1). Since `x ∈ W` and `u ∈ U ≤ W`, also `y = x - u ∈ W`, so `y ∈ X ⊓ W`.
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxUX, hxW⟩ := hx
    rw [q1_mem_sup_iff] at hxUX
    obtain ⟨u, hu, y, hy, rfl⟩ := hxUX
    rw [q1_mem_sup_iff]
    refine ⟨u, hu, y, ?_, rfl⟩
    rw [Submodule.mem_inf]
    refine ⟨hy, ?_⟩
    have huW : u ∈ W := h hu
    have hyeq : y = (u + y) - u := by abel
    rw [hyeq]
    exact W.sub_mem hxW huW

/-- The set of vectors in `ℝ³` whose coordinates sum to `0` is a subspace. -/
theorem q9_sumZero_isSubspace :
    ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 + v 1 + v 2 = 0} := by
  -- The defining condition `v 0 + v 1 + v 2 = 0` is linear, so the set is closed under the
  -- vector-space operations: `0` satisfies it, and it survives sums and scalar multiples.
  -- Package those three facts as a subspace whose underlying set is exactly this set.
  refine ⟨{ carrier := {v | v 0 + v 1 + v 2 = 0}
            zero_mem' := by simp
            add_mem' := ?_
            smul_mem' := ?_ }, rfl⟩
  · -- if `a` and `b` each have coordinate-sum `0`, so does `a + b`
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    linear_combination ha + hb
  · -- scaling by `c` multiplies the coordinate-sum by `c`, so `0` stays `0`
    intro c a ha
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    linear_combination c * ha

/-- The set of vectors in `ℝ³` with first coordinate `1` is not a subspace. -/
theorem q10_firstCoordOne_notSubspace :
    ¬ ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 = 1} := by
  -- Every subspace contains the zero vector, whose first coordinate is `0`, not `1`.
  rintro ⟨U, hU⟩
  have h0 : (0 : Fin 3 → ℝ) ∈ U := U.zero_mem
  rw [← SetLike.mem_coe, hU] at h0
  simp at h0

/-- The union of the two coordinate axes in `ℝ²` is not a subspace. -/
theorem q11_axes_notSubspace :
    ¬ ∃ U : Submodule ℝ (Fin 2 → ℝ),
      (U : Set (Fin 2 → ℝ)) = {v | v 0 * v 1 = 0} := by
  -- Both axis vectors `(1,0)` and `(0,1)` lie in the set, but their sum `(1,1)` has coordinate
  -- product `1 ≠ 0`. A subspace is closed under addition, so no subspace equals this set.
  rintro ⟨U, hU⟩
  have he0 : (![1, 0] : Fin 2 → ℝ) ∈ U := by rw [← SetLike.mem_coe, hU]; simp
  have he1 : (![0, 1] : Fin 2 → ℝ) ∈ U := by rw [← SetLike.mem_coe, hU]; simp
  have hsum : (![1, 0] + ![0, 1] : Fin 2 → ℝ) ∈ U := U.add_mem he0 he1
  rw [← SetLike.mem_coe, hU] at hsum
  simp at hsum

end Solutions.LinearAlgebra.Subspaces
