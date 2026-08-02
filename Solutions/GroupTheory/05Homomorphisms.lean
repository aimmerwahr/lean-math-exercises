import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic

namespace Solutions.GroupTheory.Homomorphisms

open CategoryTheory

variable {G H : Type*} [Group G] [Group H]

theorem q1_map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  -- The image of an inverse must undo the image of the original element.
  exact f.map_inv a

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
  -- An isomorphism preserves exactly the powers that return to the identity.
  exact e.orderOf_eq a

theorem q7_ker_range_concrete (n : ℤ) :
    n ∈ (Int.castAddHom (ZMod 6)).ker ↔ (6 : ℤ) ∣ n := by
  -- An integer becomes zero modulo `6` exactly when it is divisible by `6`.
  rw [AddMonoidHom.mem_ker]
  change (n : ZMod 6) = 0 ↔ (6 : ℤ) ∣ n
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n 6

theorem q8_cyclic_same_order_iso [IsCyclic G] [IsCyclic H]
    (hcard : Nat.card G = Nat.card H) : Nonempty (G ≃* H) := by
  -- A generator identifies each cyclic group with the same cyclic model of its cardinality.
  exact ⟨mulEquivOfCyclicCardEq hcard⟩

structure GrpObj where
  carrier : Type
  group : Group carrier

attribute [instance] GrpObj.group

theorem q9_groups_form_category : Nonempty (Category.{0} GrpObj) := by
  -- Homomorphisms compose as functions, with the identity homomorphism as a two-sided unit.
  refine ⟨{ Hom := fun X Y => X.carrier →* Y.carrier
            id := fun X => MonoidHom.id X.carrier
            comp := fun f g => g.comp f
            id_comp := by intro X Y f; ext x; rfl
            comp_id := by intro X Y f; ext x; rfl
            assoc := by intro W X Y Z f g h; ext x; rfl }⟩

inductive OneObj where
  | star

theorem q10_group_as_groupoid (K : Type) [Group K] : Nonempty (Groupoid.{0} OneObj) := by
  -- Multiplication supplies composition, and the group inverse supplies an inverse arrow.
  refine ⟨{ Hom := fun _ _ => K
            id := fun _ => 1
            comp := fun f g => f * g
            id_comp := by intro X Y f; exact one_mul f
            comp_id := by intro X Y f; exact mul_one f
            assoc := by intro W X Y Z f g h; exact mul_assoc f g h
            inv := fun f => f⁻¹
            inv_comp := by intro X Y f; exact inv_mul_cancel f
            comp_inv := by intro X Y f; exact mul_inv_cancel f }⟩

end Solutions.GroupTheory.Homomorphisms
