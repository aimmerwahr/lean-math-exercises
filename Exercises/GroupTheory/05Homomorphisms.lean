import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Homomorphisms & Isomorphisms

A group homomorphism preserves multiplication. Its kernel measures precisely what it collapses, and
its image records what it reaches. Kernels are normal, isomorphisms preserve element orders, and
Cayley's theorem realizes every group as a group of permutations. The final two questions give a
first look at categories: groups with homomorphisms form a category, while a single group is a
one-object groupoid.

Prove each statement yourself; canonical proofs live in `Solutions/GroupTheory/05Homomorphisms.lean`.
Do not commit proofs into this file. Bans are enforced when you build the project.
-/

namespace Exercises.GroupTheory.Homomorphisms

open CategoryTheory

variable {G H : Type*} [Group G] [Group H]

/-! ## Potentially helpful results -/
section

#check MonoidHom.map_inv
#check MonoidHom.mem_ker
#check Subgroup.mem_zpowers_iff
#check MulEquiv.orderOf_eq
#check ZMod.intCast_zmod_eq_zero_iff_dvd
#check mulEquivOfCyclicCardEq

end

/-- **Question 1.** A homomorphism sends inverses to inverses. -/
theorem q1_map_inv (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
  sorry


/-- **Question 2.**

A homomorphism is injective exactly when its kernel is trivial.

Prove without using `MonoidHom.ker_eq_bot_iff`. -/
theorem q2_injective_iff_ker (f : G →* H) : Function.Injective f ↔ f.ker = ⊥ := by
  sorry


/-- **Question 3.**

The kernel of every group homomorphism is a normal subgroup.

Prove without using `MonoidHom.normal_ker`. -/
theorem q3_ker_normal (f : G →* H) : f.ker.Normal := by
  sorry


/-- **Question 4.**

Cayley's theorem: every group embeds into the permutation group of its underlying set.

Prove without using `MulAction.toPermHom`. -/
theorem q4_cayley : ∃ φ : G →* Equiv.Perm G, Function.Injective φ := by
  sorry


/-- **Question 5.** A homomorphism out of a cyclic group is determined by the image of a generator. -/
theorem q5_hom_cyclic_determined (g : G) (hg : Subgroup.zpowers g = ⊤) (f h : G →* H)
    (hgen : f g = h g) : f = h := by
  sorry


/-- **Question 6.** An isomorphism preserves the order of every element. -/
theorem q6_iso_preserves_orderOf (e : G ≃* H) (a : G) : orderOf (e a) = orderOf a := by
  sorry


/-- **Question 7.** For reduction modulo `6`, the kernel is the multiples of `6` and the map is
surjective. -/
theorem q7_ker_range_concrete (n : ℤ) :
    n ∈ (Int.castAddHom (ZMod 6)).ker ↔ (6 : ℤ) ∣ n := by
  sorry


/-- **Question 8.** Two cyclic groups with the same finite cardinality are isomorphic. -/
theorem q8_cyclic_same_order_iso [IsCyclic G] [IsCyclic H]
    (hcard : Nat.card G = Nat.card H) : Nonempty (G ≃* H) := by
  sorry

/-- A group together with its carrier, used in the categorical exercise. -/
structure GrpObj where
  carrier : Type
  group : Group carrier

attribute [instance] GrpObj.group


/-- **Question 9.**

A category has objects, morphisms between objects, identities, and associative composition. Show
that bundled groups are the objects of a category whose morphisms are group homomorphisms. -/
theorem q9_groups_form_category : Nonempty (Category.{0} GrpObj) := by
  sorry

/-- A bespoke one-object type used to view a group as a groupoid. -/
inductive OneObj where
  | star


/-- **Question 10.**

A group can be viewed as a category with one object: its elements are the arrows, multiplication is
composition, and inverses make every arrow invertible. Construct that groupoid without using the
packaged one-object-category construction. -/
theorem q10_group_as_groupoid (K : Type) [Group K] : Nonempty (Groupoid.{0} OneObj) := by
  sorry

end Exercises.GroupTheory.Homomorphisms
