import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Subspaces

Subspaces of a vector space `V` over a field `K`, viewed through their lattice structure:
intersection `⊓`, sum `⊔`, when a union is a subspace, and direct sums.

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

/-- **Question 1.**

The intersection `U ⊓ W` of two subspaces consists exactly of the vectors lying in
both `U` and `W`.

Prove without using `Submodule.mem_inf`. -/
theorem q1_mem_inf_iff (U W : Submodule K V) (x : V) :
    x ∈ U ⊓ W ↔ x ∈ U ∧ x ∈ W := by
  sorry

/-- **Question 2.**

A vector lies in the sum `U ⊔ W` iff it can be written as `u + w` with `u ∈ U` and
`w ∈ W`.

Prove without using `Submodule.mem_sup` (or `Submodule.mem_sup'`). -/
theorem q2_mem_sup_iff (U W : Submodule K V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ u ∈ U, ∃ w ∈ W, u + w = x := by
  sorry

/-- **Question 3.**

The sum `U ⊔ W` is contained in `X` iff both `U` and `W` are. (Universal property:
`U ⊔ W` is the least subspace containing both.)

Prove without using `sup_le` or `sup_le_iff`. -/
theorem q3_sup_le_iff (U W X : Submodule K V) :
    U ⊔ W ≤ X ↔ U ≤ X ∧ W ≤ X := by
  sorry

/-- **Question 4.**

`U ⊔ W = W` holds iff `U ⊆ W`.

Prove without using `sup_eq_right` or `sup_eq_left`. -/
theorem q4_sup_eq_right_iff_le (U W : Submodule K V) :
    U ⊔ W = W ↔ U ≤ W := by
  sorry

/-- **Question 5.**

If `u ∈ U` but `u ∉ W`, and `w ∈ W` but `w ∉ U`, then `u + w` lies in neither `U` nor
`W`; that is, it is outside the set-theoretic union `↑U ∪ ↑W`.

Here `↑U : Set V` is the underlying set of the subspace `U`, and `↑U ∪ ↑W : Set V` is the
ordinary union of the two underlying sets. -/
theorem q5_add_notMem_union (U W : Submodule K V) {u w : V}
    (hu : u ∈ U) (hw : w ∈ W) (huW : u ∉ W) (hwU : w ∉ U) :
    u + w ∉ (↑U ∪ ↑W : Set V) := by
  sorry

/-- **Question 6.**

The union of two subspaces is itself a subspace iff one of them contains the other.

We encode "the union is a subspace" as the set equality `↑U ∪ ↑W = ↑(U ⊔ W)`: the left side
`↑U ∪ ↑W : Set V` is the ordinary union of the two underlying sets, and the right side
`↑(U ⊔ W) : Set V` is the underlying set of the smallest subspace containing both. A subset
of `V` is a subspace exactly when it coincides with the subspace it generates, so this
equality says precisely that `↑U ∪ ↑W` is already a subspace. -/
theorem q6_union_isSubspace_iff_le (U W : Submodule K V) :
    (↑U ∪ ↑W : Set V) = ↑(U ⊔ W) ↔ U ≤ W ∨ W ≤ U := by
  sorry

/-- **Question 7.**

Two subspaces `U` and `W` are disjoint iff the only vector common to both is `0`.

Prove without using `Submodule.disjoint_def` or `disjoint_iff`. -/
theorem q7_disjoint_iff_forall_eq_zero (U W : Submodule K V) :
    Disjoint U W ↔ ∀ x, x ∈ U → x ∈ W → x = 0 := by
  sorry

/-- **Question 8.**

The sum of `U` and `W` is direct (i.e. `U` and `W` are disjoint) iff every vector has
at most one decomposition as `u + w` with `u ∈ U` and `w ∈ W`. -/
theorem q8_directSum_iff_unique_decomp (U W : Submodule K V) :
    Disjoint U W ↔
      ∀ u₁ ∈ U, ∀ u₂ ∈ U, ∀ w₁ ∈ W, ∀ w₂ ∈ W,
        u₁ + w₁ = u₂ + w₂ → u₁ = u₂ ∧ w₁ = w₂ := by
  sorry

/-- **Question 9.**

Modular law: if `U ⊆ W`, then `U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W`.

Prove without using `sup_inf_assoc_of_le`. -/
theorem q9_modular_law (U W X : Submodule K V) (h : U ≤ W) :
    U ⊔ (X ⊓ W) = (U ⊔ X) ⊓ W := by
  sorry

end Exercises.LinearAlgebra.Subspaces
