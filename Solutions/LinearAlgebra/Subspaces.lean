import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic

/-!
# Solutions — LinearAlgebra / Subspaces

Canonical proofs for `Exercises/LinearAlgebra/Subspaces.lean`. Each proof builds the result
from first principles rather than invoking the library lemma the exercise asks you to avoid,
so the whole argument is visible (e.g. `q2` constructs the sum subspace by hand). These
solutions have been verified to respect those constraints.
-/

namespace Solutions.LinearAlgebra.Subspaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The intersection `U ⊓ W` consists exactly of the vectors lying in both `U` and `W`. -/
theorem q1_mem_inf_iff (U W : Submodule K V) (x : V) :
    x ∈ U ⊓ W ↔ x ∈ U ∧ x ∈ W :=
  -- Membership in the intersection of two subspaces is, by definition, membership in both;
  -- so the equivalence is immediate.
  Iff.rfl

/-- A vector lies in `U ⊔ W` iff it is a sum `u + w` with `u ∈ U`, `w ∈ W`. -/
theorem q2_mem_sup_iff (U W : Submodule K V) (x : V) :
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
theorem q3_sup_le_iff (U W X : Submodule K V) :
    U ⊔ W ≤ X ↔ U ≤ X ∧ W ≤ X := by
  constructor
  · -- If the sum sits inside `X`, so do the summands, since `U, W ≤ U ⊔ W`.
    intro h
    exact ⟨le_sup_left.trans h, le_sup_right.trans h⟩
  · -- Conversely, take any `x ∈ U ⊔ W`, write it as `u + w` (q2), and land in `X`.
    rintro ⟨hU, hW⟩ x hx
    rw [q2_mem_sup_iff] at hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    exact add_mem (hU hu) (hW hw)

/-- `U ⊔ W = W` iff `U ≤ W`. -/
theorem q4_sup_eq_right_iff_le (U W : Submodule K V) :
    U ⊔ W = W ↔ U ≤ W := by
  constructor
  · -- `U ≤ U ⊔ W = W`.
    intro h
    calc U ≤ U ⊔ W := le_sup_left
      _ = W := h
  · -- Antisymmetry: `U ⊔ W ≤ W` (by q3, since `U ≤ W` and `W ≤ W`) and `W ≤ U ⊔ W`.
    intro h
    exact le_antisymm ((q3_sup_le_iff U W W).mpr ⟨h, le_rfl⟩) le_sup_right

/-- If `u ∈ U \ W` and `w ∈ W \ U`, then `u + w ∉ ↑U ∪ ↑W`. -/
theorem q5_add_notMem_union (U W : Submodule K V) {u w : V}
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
theorem q6_union_isSubspace_iff_le (U W : Submodule K V) :
    (↑U ∪ ↑W : Set V) = ↑(U ⊔ W) ↔ U ≤ W ∨ W ≤ U := by
  constructor
  · -- Forward. If the pieces were incomparable we could pick `u ∈ U \ W` and `w ∈ W \ U`;
    -- then `u + w ∈ U ⊔ W = ↑U ∪ ↑W`, contradicting q5.
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
    exact q5_add_notMem_union U W hu hw huW hwU hmem
  · -- Backward. If say `U ≤ W`, then `U ⊔ W = W` (q4) and `↑U ∪ ↑W = ↑W`.
    rintro (h | h)
    · have hsup : U ⊔ W = W := (q4_sup_eq_right_iff_le U W).mpr h
      rw [hsup, Set.union_eq_right]
      exact fun x hx => h hx
    · have hsup : U ⊔ W = U := by
        rw [sup_comm]; exact (q4_sup_eq_right_iff_le W U).mpr h
      rw [hsup, Set.union_eq_left]
      exact fun x hx => h hx

/-- `Disjoint U W` iff the only common vector is `0`. -/
theorem q7_disjoint_iff_forall_eq_zero (U W : Submodule K V) :
    Disjoint U W ↔ ∀ x, x ∈ U → x ∈ W → x = 0 := by
  -- Disjointness of subspaces means they meet only in the zero subspace `⊥ = {0}`; so a
  -- vector lying in both must be `0`, and conversely.
  rw [disjoint_iff_inf_le]
  constructor
  · intro h x hxU hxW
    have hx : x ∈ U ⊓ W := (q1_mem_inf_iff U W x).mpr ⟨hxU, hxW⟩
    have : x ∈ (⊥ : Submodule K V) := h hx
    rwa [Submodule.mem_bot] at this
  · intro h x hx
    rw [q1_mem_inf_iff] at hx
    rw [Submodule.mem_bot]
    exact h x hx.1 hx.2

/-- The sum is direct iff decompositions `u + w` are unique. -/
theorem q8_directSum_iff_unique_decomp (U W : Submodule K V) :
    Disjoint U W ↔
      ∀ u₁ ∈ U, ∀ u₂ ∈ U, ∀ w₁ ∈ W, ∀ w₂ ∈ W,
        u₁ + w₁ = u₂ + w₂ → u₁ = u₂ ∧ w₁ = w₂ := by
  rw [q7_disjoint_iff_forall_eq_zero]
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
theorem q9_modular_law (U W X : Submodule K V) (h : U ≤ W) :
    U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W := by
  apply le_antisymm
  · -- `≤` holds in any lattice: bound each summand.
    apply sup_le
    · exact le_inf le_sup_left h
    · exact le_inf (inf_le_left.trans le_sup_right) inf_le_right
  · -- `≥` is the modular content. Take `x ∈ (U ⊔ X) ⊓ W`, write `x = u + y` with `u ∈ U`,
    -- `y ∈ X` (q2). Since `x ∈ W` and `u ∈ U ≤ W`, also `y = x - u ∈ W`, so `y ∈ X ⊓ W`.
    intro x hx
    rw [q1_mem_inf_iff] at hx
    obtain ⟨hxUX, hxW⟩ := hx
    rw [q2_mem_sup_iff] at hxUX
    obtain ⟨u, hu, y, hy, rfl⟩ := hxUX
    rw [q2_mem_sup_iff]
    refine ⟨u, hu, y, ?_, rfl⟩
    rw [q1_mem_inf_iff]
    refine ⟨hy, ?_⟩
    have huW : u ∈ W := h hu
    have hyeq : y = (u + y) - u := by abel
    rw [hyeq]
    exact W.sub_mem hxW huW

end Solutions.LinearAlgebra.Subspaces
