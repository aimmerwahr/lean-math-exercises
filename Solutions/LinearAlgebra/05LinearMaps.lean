import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Solutions.LinearAlgebra.LinearMaps

open Module LinearMap

variable {K : Type*} [Field K] {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem q1_fiber_coset (f : V →ₗ[K] W) (x₀ : V) (w : W) (h : f x₀ = w) (x : V) :
    f x = w ↔ x - x₀ ∈ ker f := by
  -- `x - x₀ ∈ ker f` means `f x - f x₀ = 0`, i.e. `f x = f x₀ = w`.
  rw [LinearMap.mem_ker, map_sub, h, sub_eq_zero]

theorem q2_injective_iff_ker (f : V →ₗ[K] W) :
    Function.Injective f ↔ ker f = ⊥ := by
  constructor
  · -- If `f` is injective, only `0` can map to `0`, so the kernel is `{0} = ⊥`.
    intro hinj
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    exact hinj (by rw [hx, map_zero])
  · -- Conversely, if `f a = f b` then `a - b` maps to `0`, so lies in `ker f = ⊥`, so `a = b`.
    intro hker a b hab
    have hmem : a - b ∈ ker f := by rw [LinearMap.mem_ker, map_sub, hab, sub_self]
    rw [hker, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem

theorem q3_inj_iff_surj [FiniteDimensional K V] (f : V →ₗ[K] V) :
    Function.Injective f ↔ Function.Surjective f := by
  -- Reduce both sides to dimension: injective means `ker f = ⊥`, surjective means `range f = ⊤`,
  -- and rank–nullity `dim range + dim ker = dim V` ties the two together.
  rw [q2_injective_iff_ker, ← LinearMap.range_eq_top]
  have hrn := f.finrank_range_add_finrank_ker
  constructor
  · intro hker
    apply Submodule.eq_top_of_finrank_eq
    rw [hker] at hrn
    simpa using hrn
  · intro hrange
    have hV : finrank K ↥(range f) = finrank K V := by rw [hrange, finrank_top]
    rw [hV] at hrn
    exact Submodule.finrank_eq_zero.mp (by omega)

theorem q4_no_inj_to_smaller [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (h : finrank K W < finrank K V) : ker f ≠ ⊥ := by
  -- If the kernel were `⊥`, rank–nullity would give `dim range = dim V`; but the range sits
  -- inside `W`, so `dim range ≤ dim W < dim V` — a contradiction.
  intro hker
  have hrn := f.finrank_range_add_finrank_ker
  rw [hker] at hrn
  simp only [finrank_bot, add_zero] at hrn
  have hle : finrank K ↥(range f) ≤ finrank K W := Submodule.finrank_le _
  omega

def proj₁ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, 0]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' c a := by funext i; fin_cases i <;> simp

@[simp] theorem proj₁_apply (v : Fin 2 → ℝ) : proj₁ v = ![v 0, 0] := rfl

def proj₃₂ : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, v 1]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' c a := by funext i; fin_cases i <;> simp

@[simp] theorem proj₃₂_apply (v : Fin 3 → ℝ) : proj₃₂ v = ![v 0, v 1] := rfl

theorem q5_projection :
    proj₁ ∘ₗ proj₁ = proj₁ ∧ ¬ Function.Injective proj₁ ∧ ¬ Function.Surjective proj₁ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Applying the projection twice is the same as once (the first coordinate is untouched).
    ext v i; fin_cases i <;> simp
  · -- `(0,1)` and `(0,0)` have the same image `(0,0)`, so `p` is not injective.
    intro hinj
    have heq : proj₁ ![0, 1] = proj₁ ![0, 0] := by ext i; fin_cases i <;> simp
    have := congrFun (hinj heq) 1
    simp at this
  · -- `(0,1)` is not in the range: every image has second coordinate `0`.
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj ![0, 1]
    have := congrFun hv 1
    simp at this

theorem q6_project_surj_not_inj :
    Function.Surjective proj₃₂ ∧ ¬ Function.Injective proj₃₂ := by
  constructor
  · -- Any `(a, b)` is the image of `(a, b, 0)`.
    intro w
    exact ⟨![w 0, w 1, 0], by ext i; fin_cases i <;> simp⟩
  · -- `(0,0,0)` and `(0,0,1)` share the image `(0,0)`, so the map is not injective.
    intro hinj
    have heq : proj₃₂ ![0, 0, 0] = proj₃₂ ![0, 0, 1] := by ext i; fin_cases i <;> simp
    have := congrFun (hinj heq) 2
    simp at this

theorem q7_ker_comp_injective {U : Type*} [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) (hg : Function.Injective g) :
    ker (g ∘ₗ f) = ker f := by
  -- `x ∈ ker (g ∘ f)` says `g (f x) = 0`; since `g` is injective it sends only `0` to `0`, so this
  -- is `f x = 0`, i.e. `x ∈ ker f`.
  ext x
  rw [mem_ker, mem_ker, comp_apply, map_eq_zero_iff g hg]

theorem q8_finrank_le_of_map [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) : finrank K V ≤ finrank K W + finrank K (ker f) := by
  -- Rank–nullity reads `dim (range f) + dim (ker f) = dim V`, and the range, sitting inside `W`,
  -- has dimension at most `dim W`. Substituting the bound gives the inequality.
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hr := Submodule.finrank_le (LinearMap.range f)
  omega

end Solutions.LinearAlgebra.LinearMaps
