import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / LinearMaps

A **linear map** `f : V → W` respects addition and scalar multiplication. Its **kernel** is the
subspace `ker f = {v : f v = 0}`, and its **range** is the subspace
`range f = {w | ∃ v, f v = w}`. If `f x₀ = w`, then the fiber over `w` is precisely
`{x | x - x₀ ∈ ker f}`; consequently, `f` is injective exactly when `ker f = ⊥`.

When `V` is finite-dimensional, rank–nullity gives
`dim (range f) + dim (ker f) = dim V`. Applied to an endomorphism `f : V →ₗ[K] V`, this implies
that injectivity and surjectivity are equivalent.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/05LinearMaps.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project.
-/

namespace Exercises.LinearAlgebra.LinearMaps

open Module LinearMap

variable {K : Type*} [Field K] {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Membership in the kernel, and pushing a map through a subtraction; `x ∈ ⊥ ↔ x = 0`.
#check @LinearMap.mem_ker
#check @map_sub
#check @map_zero
#check @Submodule.mem_bot

-- Rank–nullity, and the dimension bound for a range.
#check @LinearMap.finrank_range_add_finrank_ker
#check @Submodule.finrank_le

end


/-- **Question 1.**

The solution set of `f x = w` is a coset of the kernel: if `f x₀ = w`, then `f x = w` holds iff
`x - x₀ ∈ ker f`. -/
theorem q1_fiber_coset (f : V →ₗ[K] W) (x₀ : V) (w : W) (h : f x₀ = w) (x : V) :
    f x = w ↔ x - x₀ ∈ ker f := by
  sorry


/-- **Question 2.**

A linear map is injective iff its kernel is trivial: `Injective f ↔ ker f = ⊥`.

Prove without using `LinearMap.ker_eq_bot`. -/
theorem q2_injective_iff_ker (f : V →ₗ[K] W) :
    Function.Injective f ↔ ker f = ⊥ := by
  sorry


/-- **Question 3.**

A linear map is surjective iff its range is the whole codomain: `Surjective f ↔ range f = ⊤`.

Prove without using `LinearMap.range_eq_top`. -/
theorem q3_surjective_iff_range (f : V →ₗ[K] W) :
    Function.Surjective f ↔ range f = ⊤ := by
  sorry


/-- **Question 4.**

On a finite-dimensional space, an operator is injective iff it is surjective:
for `f : V →ₗ[K] V`, `Injective f ↔ Surjective f`.

Prove without using `LinearMap.injective_iff_surjective`. -/
theorem q4_inj_iff_surj [FiniteDimensional K V] (f : V →ₗ[K] V) :
    Function.Injective f ↔ Function.Surjective f := by
  sorry


/-- **Question 5.**

The quantitative form of Question 4: for any `f : V → W`, `dim V ≤ dim W + dim (ker f)`. -/
theorem q5_finrank_le_of_map [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) : finrank K V ≤ finrank K W + finrank K (ker f) := by
  sorry


/-- **Question 6.**

A linear map into a strictly lower-dimensional space cannot be injective — it must have nonzero
kernel: if `dim W < dim V`, then `ker f ≠ ⊥`. -/
theorem q6_no_inj_to_smaller [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (h : finrank K W < finrank K V) : ker f ≠ ⊥ := by
  sorry


/-- The projection of `ℝ²` onto its first coordinate, `(x, y) ↦ (x, 0)`. -/
def proj₁ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, 0]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' c a := by funext i; fin_cases i <;> simp

-- Labels "projecting to the first coordinate" as a simp lemma so that `simp` can
-- automatically unfold `proj₁ v` to `![v 0, 0]` in later proofs.
@[simp] theorem proj₁_apply (v : Fin 2 → ℝ) : proj₁ v = ![v 0, 0] := rfl

/-- The projection `ℝ³ → ℝ²`, `(x, y, z) ↦ (x, y)`. -/
def proj₃₂ : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, v 1]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' c a := by funext i; fin_cases i <;> simp

-- Labels "projecting to the first two coordinates" as a simp lemma so that `simp` can
-- automatically unfold `proj₃₂ v` to `![v 0, v 1]` in later proofs.
@[simp] theorem proj₃₂_apply (v : Fin 3 → ℝ) : proj₃₂ v = ![v 0, v 1] := rfl


/-- **Question 7.**

The projection `p (x, y) = (x, 0)` on `ℝ²` is idempotent (`p ∘ p = p`) but is neither injective
nor surjective. -/
theorem q7_projection :
    proj₁ ∘ₗ proj₁ = proj₁ ∧ ¬ Function.Injective proj₁ ∧ ¬ Function.Surjective proj₁ := by
  sorry


/-- **Question 8.**

The projection `g (x, y, z) = (x, y)` from `ℝ³` to `ℝ²` is surjective but not injective. -/
theorem q8_project_surj_not_inj :
    Function.Surjective proj₃₂ ∧ ¬ Function.Injective proj₃₂ := by
  sorry


/-- **Question 9.**

Composing with an injective map on the outside does not change the kernel: if `g` is injective,
then `ker (g ∘ f) = ker f`. -/
theorem q9_ker_comp_injective {U : Type*} [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) (hg : Function.Injective g) :
    ker (g ∘ₗ f) = ker f := by
  sorry


end Exercises.LinearAlgebra.LinearMaps
