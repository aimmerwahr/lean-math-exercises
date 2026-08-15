import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Opposite
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic

namespace Solutions.GroupTheory.Homomorphisms

open CategoryTheory

variable {G H : Type*} [Group G] [Group H]


theorem q1_map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  -- The image of an inverse undoes the image of the original element.
  apply eq_inv_of_mul_eq_one_left
  rw [← f.map_mul, inv_mul_cancel, f.map_one]


theorem q2_injective_iff_ker (f : G →* H) : Function.Injective f ↔ f.ker = ⊥ := by
  constructor
  · intro hinj
    apply bot_unique
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact hinj (by simpa using hx)
  · intro hker x y hxy
    -- Equal images make `x y⁻¹` invisible to f; a trivial kernel then forces `x = y`.
    have hmem : x * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp [f.map_mul, f.map_inv, hxy]
    rw [hker, Subgroup.mem_bot] at hmem
    simpa [mul_inv_eq_one] using hmem


theorem q3_ker_normal (f : G →* H) : f.ker.Normal := by
  constructor
  intro n hn g
  -- Conjugation changes the image to `f g * 1 * (f g)⁻¹`, so it stays in the kernel.
  rw [MonoidHom.mem_ker] at hn ⊢
  simp [f.map_mul, f.map_inv, hn]


theorem q4_cayley : ∃ φ : G →* Equiv.Perm G, Function.Injective φ := by
  -- Let each element act by left multiplication; evaluating at the identity recovers that element.
  let φ : G →* Equiv.Perm G :=
    { toFun := Equiv.mulLeft
      map_one' := Equiv.mulLeft_one
      map_mul' := Equiv.mulLeft_mul }
  refine ⟨φ, ?_⟩
  intro a b hab
  have h := congrArg (fun p : Equiv.Perm G => p 1) hab
  simpa [φ] using h


theorem q5_hom_cyclic_determined (g : G) (hg : Subgroup.zpowers g = ⊤) (f h : G →* H)
    (hgen : f g = h g) : f = h := by
  ext x
  -- Since g generates G, x is a (possibly negative) power of g, and both maps preserve that power.
  have hx : x ∈ Subgroup.zpowers g := by rw [hg]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hk, f.map_zpow, h.map_zpow, hgen]


theorem q6_iso_preserves_orderOf (e : G ≃* H) (a : G) : orderOf (e a) = orderOf a := by
  -- Each direction says that the image of an identity power is again an identity power.
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, ← map_pow e, pow_orderOf_eq_one, map_one]
  · rw [orderOf_dvd_iff_pow_eq_one]
    apply e.injective
    rw [map_pow, pow_orderOf_eq_one, map_one]


theorem q7_mod_six_kernel_examples :
    (12 : ℤ) ∈ (Int.castAddHom (ZMod 6)).ker ∧ (5 : ℤ) ∉ (Int.castAddHom (ZMod 6)).ker := by
  constructor
  · rw [AddMonoidHom.mem_ker]
    change ((12 : ℤ) : ZMod 6) = ((0 : ℤ) : ZMod 6)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  · rw [AddMonoidHom.mem_ker]
    intro h
    change ((5 : ℤ) : ZMod 6) = ((0 : ℤ) : ZMod 6) at h
    rw [ZMod.intCast_eq_intCast_iff'] at h
    norm_num at h


theorem q8_zmod_six_generated_by_one : AddSubgroup.zmultiples (1 : ZMod 6) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨n, ?_⟩
  simp


structure GrpObj where
  carrier : Type
  group : Group carrier

attribute [instance] GrpObj.group


structure OneObjectGroupoid (K : Type) [Group K] where
  identity : K
  composition : K → K → K
  inverse : K → K
  identity_eq : identity = 1
  composition_eq : ∀ f g, composition f g = g * f
  inverse_eq : ∀ f, inverse f = f⁻¹
  id_comp : ∀ f, composition identity f = f
  comp_id : ∀ f, composition f identity = f
  assoc : ∀ f g h, composition (composition f g) h = composition f (composition g h)
  inv_comp : ∀ f, composition (inverse f) f = identity
  comp_inv : ∀ f, composition f (inverse f) = identity


theorem q9_group_as_groupoid (K : Type) [Group K] : Nonempty (OneObjectGroupoid K) := by
  refine ⟨{ identity := 1
            composition := fun f g => g * f
            inverse := fun f => f⁻¹
            identity_eq := rfl
            composition_eq := by intro f g; rfl
            inverse_eq := by intro f; rfl
            id_comp := by intro f; exact mul_one f
            comp_id := by intro f; exact one_mul f
            assoc := by intro f g h; exact (mul_assoc h g f).symm
            inv_comp := by intro f; exact mul_inv_cancel f
            comp_inv := by intro f; exact inv_mul_cancel f }⟩


theorem q10_q8_not_iso_d4 : IsEmpty (QuaternionGroup 2 ≃* DihedralGroup 4) := by
  -- Isomorphisms carry the solution set of `x² = 1` bijectively to the corresponding solution set.
  rw [isEmpty_iff]
  intro e
  have hcard : Fintype.card {x : QuaternionGroup 2 // x * x = 1}
      = Fintype.card {y : DihedralGroup 4 // y * y = 1} :=
    Fintype.card_congr
      { toFun := fun x => ⟨e x, by rw [← map_mul, x.2, map_one]⟩
        invFun := fun y => ⟨e.symm y, by rw [← map_mul, y.2, map_one]⟩
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
  have h2 : Fintype.card {x : QuaternionGroup 2 // x * x = 1} = 2 := by decide
  have h6 : Fintype.card {y : DihedralGroup 4 // y * y = 1} = 6 := by decide
  rw [h2, h6] at hcard
  exact absurd hcard (by decide)


theorem q11_opposite_iso :
    ∃ e : G ≃* Gᵐᵒᵖ, ∀ x, e x = MulOpposite.op x⁻¹ := by
  refine ⟨{ toFun := fun x => MulOpposite.op x⁻¹
            invFun := fun y => (MulOpposite.unop y)⁻¹
            left_inv := fun x => by simp
            right_inv := fun y => by simp
            map_mul' := fun x y => by simp [mul_inv_rev] }, fun x => rfl⟩

end Solutions.GroupTheory.Homomorphisms
