import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.Dimension

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (U W : Submodule K V)

/-- Equal finite dimension plus inclusion forces equality. -/
theorem q1_rigidity (h : U ≤ W) (hdim : finrank K U = finrank K W) : U = W := by
  -- If `U` were a *proper* subspace of `W`, its dimension would be strictly smaller — but the
  -- dimensions are equal. So there is no room: `U = W`.
  by_contra hne
  have hlt : U < W := lt_of_le_of_ne h hne
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- A subspace has the full dimension of the space iff it is everything. -/
theorem q2_eq_top_iff : finrank K U = finrank K V ↔ U = ⊤ := by
  constructor
  · -- `U` has the same dimension as `⊤` (the whole space), and `U ≤ ⊤`, so by q1 `U = ⊤`.
    intro hU
    exact q1_rigidity U ⊤ le_top (by rw [finrank_top]; exact hU)
  · -- Conversely `⊤` has the dimension of the whole space.
    intro hU
    rw [hU, finrank_top]

/-- Disjoint subspaces: the dimension of the sum is the sum of the dimensions. -/
theorem q3_dim_directSum (h : Disjoint U W) :
    finrank K ↥(U ⊔ W) = finrank K U + finrank K W := by
  -- In the dimension formula the intersection term is `dim ⊥ = 0`, leaving `dim (U ⊔ W) =
  -- dim U + dim W`.
  have hform := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [h.eq_bot, finrank_bot, add_zero] at hform
  exact hform

/-- A numerical use of the dimension formula. -/
theorem q4_numeric_formula (hU : finrank K U = 3) (hW : finrank K W = 4)
    (hsup : finrank K ↥(U ⊔ W) = 5) : finrank K ↥(U ⊓ W) = 2 := by
  -- `dim(U ⊔ W) + dim(U ⊓ W) = dim U + dim W`, i.e. `5 + dim(U ⊓ W) = 3 + 4`.
  have hform := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

/-- Two planes in a 3-space meet in at least a line. -/
theorem q5_planes_meet (hV : finrank K V = 3) (hU : finrank K U = 2)
    (hW : finrank K W = 2) : 1 ≤ finrank K ↥(U ⊓ W) := by
  -- The formula gives `dim(U ⊔ W) + dim(U ⊓ W) = 4`; since the sum lives in a 3-dimensional
  -- space, `dim(U ⊔ W) ≤ 3`, forcing `dim(U ⊓ W) ≥ 1`.
  have hform := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hle : finrank K ↥(U ⊔ W) ≤ finrank K V := Submodule.finrank_le _
  omega

/-- `dim ℝ³ = 3`. -/
theorem q6_finrank_pi : finrank ℝ (Fin 3 → ℝ) = 3 := by
  -- The standard `n`-tuple space has dimension `n`.
  simp

omit [FiniteDimensional K V] in
/-- A line has dimension `1`. -/
theorem q7_finrank_span_singleton (v : V) (hv : v ≠ 0) :
    finrank K (Submodule.span K {v}) = 1 := by
  -- The span of one nonzero vector is a line.
  exact finrank_span_singleton hv

end Solutions.LinearAlgebra.Dimension
