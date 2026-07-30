import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Basis

A **basis** of a vector space `V` is a family of vectors that is at once **linearly independent**
and **spanning**. These two properties combine into the single fact that makes a basis useful:
every vector of `V` is a *unique* finite linear combination of the basis vectors. Independence
gives the uniqueness of that expression, spanning gives its existence, and together they set up
the **coordinate isomorphism** `V ≅ Kⁿ` that lets us compute in an abstract space.

A basis also governs linear maps: a linear map is completely determined by its values on a
basis, and those values may be prescribed arbitrarily — so a basis of `V` and a choice of one
vector of `W` per basis vector are the same thing as a linear map `V → W`. Finally, dimension
constrains bases: in `Kⁿ` no more than `n` vectors can be independent and no fewer than `n` can
span.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/Basis.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project (a proof using a banned lemma, directly or via `simp`/`exact?`, fails the
build).
-/

namespace Exercises.LinearAlgebra.Basis

open Module

variable {K : Type*} [Field K] {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n : ℕ} (b : Basis (Fin n) K V)

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- A basis is linearly independent, and over a finite index this unfolds to: a vanishing
-- combination has all-zero coefficients.
#check @Basis.linearIndependent
#check @Fintype.linearIndependent_iff

-- Expand a vector in its coordinates, and push a linear map through a sum / a scalar.
#check @Basis.sum_repr
#check @map_sum
#check @map_smul

-- Build a linear map from prescribed values on the basis, and read those values back.
#check @Basis.constr
#check @Basis.constr_basis

-- An independent family of the right size *is* a basis; the dimension of `Kⁿ`; the size
-- bounds independence and spanning must obey.
#check @basisOfLinearIndependentOfCardEqFinrank
#check @Module.finrank_fin_fun
#check @LinearIndependent.fintype_card_le_finrank
#check @finrank_span_le_card

end

/-- **Question 1.**

For a basis `(bᵢ)`, coordinates are unique: if `∑ᵢ cᵢ bᵢ = ∑ᵢ dᵢ bᵢ`, then `cᵢ = dᵢ` for every
`i`.

Prove without using `Basis.ext_elem`. -/
theorem q1_coords_unique (c d : Fin n → K)
    (h : ∑ i, c i • b i = ∑ i, d i • b i) : c = d := by
  sorry

/-- **Question 2.**

A linear map is determined by its values on a basis: if `f (bᵢ) = g (bᵢ)` for every `i`, then
`f = g`.

Prove without using `Basis.ext`. -/
theorem q2_map_determined (f g : V →ₗ[K] W) (h : ∀ i, f (b i) = g (b i)) : f = g := by
  sorry

/-- **Question 3.**

The basis values may be prescribed arbitrarily: given any target vectors `(wᵢ)` in `W`, there is
a linear map `f : V → W` with `f (bᵢ) = wᵢ` for every `i`. -/
theorem q3_prescribe_map (w : Fin n → W) : ∃ f : V →ₗ[K] W, ∀ i, f (b i) = w i := by
  sorry

/-- **Question 4.**

The vectors `(1,1)` and `(1,−1)` form a basis of `ℝ²`. -/
theorem q4_isBasis_concrete :
    ∃ B : Basis (Fin 2) ℝ (Fin 2 → ℝ), ⇑B = ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
  sorry

/-- **Question 5.**

The coordinates of `(3,1)` in the basis `{(1,1), (1,−1)}` are `(2,1)`: that is,
`2 • (1,1) + 1 • (1,−1) = (3,1)`. -/
theorem q5_coords_concrete :
    (2 : ℝ) • (![1, 1] : Fin 2 → ℝ) + (1 : ℝ) • ![1, -1] = ![3, 1] := by
  sorry

/-- **Question 6.**

The vector `(1,1,0)` extends to a basis of `ℝ³`: there is a basis of `ℝ³` whose first vector is
`(1,1,0)`. -/
theorem q6_extend_concrete :
    ∃ B : Basis (Fin 3) ℝ (Fin 3 → ℝ), B 0 = ![1, 1, 0] := by
  sorry

/-- **Question 7.**

Any three vectors in `ℝ²` are linearly dependent. -/
theorem q7_too_many_dependent (v : Fin 3 → (Fin 2 → ℝ)) : ¬ LinearIndependent ℝ v := by
  sorry

/-- **Question 8.**

No single vector spans `ℝ²`. -/
theorem q8_too_few_dont_span : ¬ ∃ v : Fin 2 → ℝ, Submodule.span ℝ {v} = ⊤ := by
  sorry

/-- **Question 9.**

A linear map that carries a basis to a linearly independent family is injective: if the images
`f (b₀), …, f (b_{n-1})` are linearly independent, then `f` is injective. -/
theorem q9_indep_image_injective (f : V →ₗ[K] W)
    (hf : LinearIndependent K fun i => f (b i)) : Function.Injective f := by
  sorry

end Exercises.LinearAlgebra.Basis
