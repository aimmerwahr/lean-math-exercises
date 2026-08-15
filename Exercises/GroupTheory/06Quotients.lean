import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Normal Subgroups & Quotients

A normal subgroup is one closed under conjugation, which is exactly what allows its cosets to become
a group. Quotients organize homomorphisms: every kernel is normal, every normal subgroup is a
kernel, and the first isomorphism theorem identifies `G / ker f` with the image of `f`. The later
questions connect this construction to abelianization, symmetric groups, and exact sequences.

Prove each statement yourself; canonical proofs live in `Solutions/GroupTheory/06Quotients.lean`.
Do not commit proofs into this file. Bans are enforced when you build the project.
-/

namespace Exercises.GroupTheory.Quotients

variable {G H : Type*} [Group G] [Group H]

/-! ## Potentially helpful results -/
section

#check Subgroup.Normal.conj_mem
#check Subgroup.mul_mem_iff_of_index_two
#check QuotientGroup.rangeKerLift
#check QuotientGroup.lift
#check QuotientGroup.map
#check MonoidHom.toMulEquiv
#check commutator_eq_closure
#check Subgroup.closure_le
#check QuotientGroup.eq_one_iff
#check alternatingGroup_eq_sign_ker

end

/-- **Question 1.** A subgroup is normal exactly when it is closed under every conjugation; this is
the conjugation form of the condition that left and right cosets agree. -/
theorem q1_normal_iff_conjugates (N : Subgroup G) :
    N.Normal ↔ ∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N := by
  sorry


/-- **Question 2.**

A subgroup of index `2` is normal.

Prove without using `Subgroup.normal_of_index_eq_two`. -/
theorem q2_index_two_normal (N : Subgroup G) (hindex : N.index = 2) : N.Normal := by
  sorry


/-- **Question 3.**

The first isomorphism theorem: quotienting by a homomorphism's kernel gives its image.

Prove without using `QuotientGroup.quotientKerEquivRange`. -/
theorem q3_first_iso (f : G →* H) : Nonempty (G ⧸ f.ker ≃* f.range) := by
  sorry


/-- **Question 4.** Every kernel is normal, and a normal subgroup is the kernel of its quotient
projection.

Prove without using `MonoidHom.normal_ker` or `QuotientGroup.ker_mk'`. -/
theorem q4_normal_iff_kernel (f : G →* H) (N : Subgroup G) [N.Normal] :
    f.ker.Normal ∧ (QuotientGroup.mk' N).ker = N := by
  sorry


/-- **Question 5.** The third isomorphism theorem: if `N ≤ M` are normal, then quotienting by `N`
and then by the image of `M` is the same as quotienting by `M`.

Prove without using `QuotientGroup.quotientQuotientEquivQuotient`. -/
theorem q5_third_iso (N M : Subgroup G) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ Subgroup.map (QuotientGroup.mk' N) M ≃* G ⧸ M) := by
  sorry


/-- **Question 6.** If `f : G →* A` has an abelian target, then every commutator lies in the
kernel of `f`. This is the fact that makes the quotient by the commutator subgroup possible.

Prove without using `Abelianization.commutator_subset_ker`. -/
theorem q6_commutator_le_ker {A : Type*} [CommGroup A] (f : G →* A) :
    commutator G ≤ f.ker := by
  sorry


/-- **Question 7.** Use the preceding containment to construct the map from the abelianization
`G / [G,G]` to an abelian target. It agrees with `f` on every element of `G`.

Prove without using `Abelianization.lift`. -/
theorem q7_abelianization {A : Type*} [CommGroup A] (f : G →* A) :
    ∃ F : Abelianization G →* A, ∀ g : G, F (Abelianization.of g) = f g := by
  sorry


/-- **Question 8.** The alternating subgroup of `S₃` is the kernel of sign, so the corresponding
quotient is isomorphic to the image of sign. -/
theorem q8_quotient_concrete :
    Nonempty (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3) ≃*
      (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).range) := by
  sorry


/-- **Question 9.** Quotienting by the trivial subgroup returns `G`, while quotienting by all of
`G` produces a trivial group.

Prove without using `QuotientGroup.quotientBot` or
`QuotientGroup.subsingleton_quotient_top`. -/
theorem q9_quotient_trivial : Nonempty (G ⧸ (⊥ : Subgroup G) ≃* G) ∧
    Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  sorry


/-- **Question 10.** If the quotient of a group by its center is cyclic, the group is abelian.

Prove without using `isMulCommutative_of_isCyclic_quotient_center_self` or
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`. -/
theorem q10_quotient_center_cyclic_abelian [IsCyclic (G ⧸ Subgroup.center G)] (a b : G) :
    a * b = b * a := by
  sorry


/-- The inclusion of the first factor of a product. -/
def firstFactor (A B : Type*) [Group A] [Group B] : A →* A × B where
  toFun := fun a => (a, 1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

/-- The projection onto the second factor of a product. -/
def secondProjection (A B : Type*) [Group A] [Group B] : A × B →* B where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **Question 11.**

The maps `A → A × B → B` form a short exact sequence: the first map is injective, the second is
surjective, and the image of the first is the kernel of the second. -/
theorem q11_short_exact_sequence (A B : Type*) [Group A] [Group B] :
    Function.Injective (firstFactor A B) ∧ Function.Surjective (secondProjection A B) ∧
      (firstFactor A B).range = (secondProjection A B).ker := by
  sorry

end Exercises.GroupTheory.Quotients
