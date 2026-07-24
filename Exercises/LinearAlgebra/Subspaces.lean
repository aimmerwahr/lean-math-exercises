import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Exercises — LinearAlgebra / Subspaces

Fix a field `K` and a `K`-vector space `V`. A **subspace** is a subset that contains `0` and
is closed under addition and scalar multiplication — equivalently, a nonempty subset closed
under linear combinations. Subspaces are the sub-objects of linear algebra: kernels, images,
solution sets of homogeneous systems, and spans are all subspaces.

The subspaces of `V`, ordered by inclusion, form a **complete lattice**. The meet is
intersection, `U ⊓ W = U ∩ W`, which is always a subspace; the join
`U ⊔ W = U + W = { u + w | u ∈ U, w ∈ W }` is the *smallest* subspace containing both — note
the set-theoretic union itself is usually **not** a subspace. The sum `U + W` and the
interplay of `∩` and `+` are the workhorses of the topic. A sum is **direct**, written
`U ⊕ W`, exactly when the two pieces meet only in `0`; then every vector of `U + W` has a
*unique* decomposition `u + w`.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/Subspaces.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma (e.g. "Prove without
using `Submodule.mem_sup`") — the point is to rebuild that result from more primitive facts.
These
bans are enforced automatically when you build the project: if a proof uses a banned lemma
(directly or via `simp`/`omega`/`exact?`) the build fails. You don't need to do anything to
enable it.
-/

namespace Exercises.LinearAlgebra.Subspaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- A subspace is closed under `+`, `-`, and scalar `•`, and contains `0`.
#check @Submodule.add_mem
#check @Submodule.sub_mem
#check @Submodule.smul_mem
#check @Submodule.zero_mem

-- The order on subspaces: each summand sits below the sum `⊔`, the meet `⊓` below each.
#check @le_sup_left
#check @le_sup_right
#check @le_inf
#check @inf_le_left
#check @inf_le_right

-- Placing a vector into a sum, and switching between `x ∈ (↑U : Set V)` and `x ∈ U`.
#check @Submodule.mem_sup_left
#check @Submodule.mem_sup_right
#check @SetLike.mem_coe

-- `x ∈ ⊥ ↔ x = 0`, and one convenient way to unfold `Disjoint`.
#check @Submodule.mem_bot
#check @disjoint_iff_inf_le

end

/-- **Question 1.**

A vector lies in the sum `U ⊔ W` iff it can be written as `u + w` with `u ∈ U` and
`w ∈ W`.

Prove without using `Submodule.mem_sup` (or `Submodule.mem_sup'`). -/
theorem q1_mem_sup_iff (U W : Submodule K V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ u ∈ U, ∃ w ∈ W, u + w = x := by
  sorry

/-- **Question 2.**

The sum `U ⊔ W` is contained in `X` iff both `U` and `W` are. (Universal property:
`U ⊔ W` is the least subspace containing both.)

Prove without using `sup_le` or `sup_le_iff`. -/
theorem q2_sup_le_iff (U W X : Submodule K V) :
    U ⊔ W ≤ X ↔ U ≤ X ∧ W ≤ X := by
  sorry

/-- **Question 3.**

`U ⊔ W = W` holds iff `U ⊆ W`.

Prove without using `sup_eq_right` or `sup_eq_left`. -/
theorem q3_sup_eq_right_iff_le (U W : Submodule K V) :
    U ⊔ W = W ↔ U ≤ W := by
  sorry

/-- **Question 4.**

If `u ∈ U` but `u ∉ W`, and `w ∈ W` but `w ∉ U`, then `u + w` lies in neither `U` nor
`W`; that is, it is outside the set-theoretic union `↑U ∪ ↑W`.

Here `↑U : Set V` is the underlying set of the subspace `U`, and `↑U ∪ ↑W : Set V` is the
ordinary union of the two underlying sets. -/
theorem q4_add_notMem_union (U W : Submodule K V) {u w : V}
    (hu : u ∈ U) (hw : w ∈ W) (huW : u ∉ W) (hwU : w ∉ U) :
    u + w ∉ (↑U ∪ ↑W : Set V) := by
  sorry

/-- **Question 5.**

The union of two subspaces is itself a subspace iff one of them contains the other.

We encode "the union is a subspace" as the set equality `↑U ∪ ↑W = ↑(U ⊔ W)`: the left side
`↑U ∪ ↑W : Set V` is the ordinary union of the two underlying sets, and the right side
`↑(U ⊔ W) : Set V` is the underlying set of the smallest subspace containing both. A subset
of `V` is a subspace exactly when it coincides with the subspace it generates, so this
equality says precisely that `↑U ∪ ↑W` is already a subspace. -/
theorem q5_union_isSubspace_iff_le (U W : Submodule K V) :
    (↑U ∪ ↑W : Set V) = ↑(U ⊔ W) ↔ U ≤ W ∨ W ≤ U := by
  sorry

/-- **Question 6.**

Two subspaces `U` and `W` are disjoint iff the only vector common to both is `0`.

Prove without using `Submodule.disjoint_def` or `disjoint_iff`. -/
theorem q6_disjoint_iff_forall_eq_zero (U W : Submodule K V) :
    Disjoint U W ↔ ∀ x, x ∈ U → x ∈ W → x = 0 := by
  sorry

/-- **Question 7.**

The sum of `U` and `W` is direct (i.e. `U` and `W` are disjoint) iff every vector has
at most one decomposition as `u + w` with `u ∈ U` and `w ∈ W`. -/
theorem q7_directSum_iff_unique_decomp (U W : Submodule K V) :
    Disjoint U W ↔
      ∀ u₁ ∈ U, ∀ u₂ ∈ U, ∀ w₁ ∈ W, ∀ w₂ ∈ W,
        u₁ + w₁ = u₂ + w₂ → u₁ = u₂ ∧ w₁ = w₂ := by
  sorry

/-- **Question 8.**

Modular law: if `U ⊆ W`, then `U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W`.

Prove without using `sup_inf_assoc_of_le`. -/
theorem q8_modular_law (U W X : Submodule K V) (h : U ≤ W) :
    U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W := by
  sorry

/-- **Question 9.**

The set of vectors in `ℝ³` whose coordinates sum to `0` is a subspace: produce a subspace of
`ℝ³` whose underlying set is exactly `{v | v 0 + v 1 + v 2 = 0}`.

(`ℝ³` is modeled as `Fin 3 → ℝ`, so `v 0`, `v 1`, `v 2` are the three coordinates.) -/
theorem q9_sumZero_isSubspace :
    ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 + v 1 + v 2 = 0} := by
  sorry

/-- **Question 10.**

Show that the set of vectors in `ℝ³` whose first coordinate equals `1` is not a subspace: no
subspace has underlying set `{v | v 0 = 1}`. -/
theorem q10_firstCoordOne_notSubspace :
    ¬ ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 = 1} := by
  sorry

/-- **Question 11.**

Show that the set `{v : ℝ² | v 0 * v 1 = 0}` — the union of the two coordinate axes — is not a
subspace. -/
theorem q11_axes_notSubspace :
    ¬ ∃ U : Submodule ℝ (Fin 2 → ℝ),
      (U : Set (Fin 2 → ℝ)) = {v | v 0 * v 1 = 0} := by
  sorry

end Exercises.LinearAlgebra.Subspaces
