import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Dimension

All bases of a finite-dimensional space have the same size, so "number of basis vectors" is an
invariant: the **dimension** `dim V`. Dimension controls subspaces tightly — a subspace has
dimension at most that of the whole space, with equality only when it *is* the whole space — and
the two operations `+` and `∩` on subspaces are linked by the **dimension formula**
`dim(U + W) + dim(U ∩ W) = dim U + dim W`. From this one identity flow both the direct-sum count
and useful numerical consequences for intersecting subspaces.

Throughout, `dim` is `Module.finrank K`, a natural number (finite-dimensional `V`).

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/04Dimension.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project.
-/

namespace Exercises.LinearAlgebra.Dimension

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (U W : Submodule K V)

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- The dimension formula, and the dimension of a subspace is bounded by that of the space.
#check @Submodule.finrank_sup_add_finrank_inf_eq
#check @Submodule.finrank_le

-- A strictly larger subspace has strictly larger dimension.
#check @Submodule.finrank_lt_finrank_of_lt

-- Dimensions of the extreme subspaces, and of a line.
#check @finrank_bot
#check @finrank_top
#check @finrank_span_singleton
#check @Disjoint.eq_bot

end


/-- **Question 1.**

If `U ≤ W` and `dim U = dim W` (finite dimension), then `U = W`.

Prove without using `Submodule.eq_of_le_of_finrank_eq`. -/
theorem q1_rigidity (h : U ≤ W) (hdim : finrank K U = finrank K W) : U = W := by
  sorry


/-- **Question 2.**

A subspace has the full dimension of the space iff it is the whole space:
`dim U = dim V ↔ U = ⊤`. -/
theorem q2_eq_top_iff : finrank K U = finrank K V ↔ U = ⊤ := by
  sorry


/-- **Question 3.**

If `U` and `W` meet only in `0`, the dimension of their sum is the sum of their dimensions:
`Disjoint U W → dim (U ⊔ W) = dim U + dim W`. -/
theorem q3_dim_directSum (h : Disjoint U W) :
    finrank K ↥(U ⊔ W) = finrank K U + finrank K W := by
  sorry


/-- **Question 4.**

If `dim U = 3`, `dim W = 4`, and `dim (U + W) = 5`, then `dim (U ∩ W) = 2`. -/
theorem q4_numeric_formula (hU : finrank K U = 3) (hW : finrank K W = 4)
    (hsup : finrank K ↥(U ⊔ W) = 5) : finrank K ↥(U ⊓ W) = 2 := by
  sorry


omit [FiniteDimensional K V] in


/-- **Question 5.**

The line spanned by a nonzero vector has dimension `1`. -/
theorem q5_finrank_span_singleton (v : V) (hv : v ≠ 0) :
    finrank K (Submodule.span K {v}) = 1 := by
  sorry

end Exercises.LinearAlgebra.Dimension
