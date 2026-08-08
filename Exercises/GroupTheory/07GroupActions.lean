import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Group Actions

A group action lets a group move the points of a set. Its orbits divide the set into the regions
that can be reached from one another, while the stabilizer of a point records the symmetries that
leave it fixed. The orbit–stabilizer correspondence turns this geometry into counting. For the
conjugation action it becomes the class equation, with strong consequences such as Cauchy's
theorem and the nontriviality of the centre of a finite `p`-group.

Prove each statement yourself; canonical proofs live in `Solutions/GroupTheory/07GroupActions.lean`.
Do not commit proofs into this file. Bans are enforced when you build the project.
-/

namespace Exercises.GroupTheory.GroupActions

variable {G X : Type*} [Group G] [MulAction G X]

/-! ## Potentially helpful results -/
section

-- Moving within an orbit and comparing two orbits.
#check MulAction.mem_orbit
#check MulAction.mem_orbit_iff
#check MulAction.mem_orbit_symm
#check MulAction.orbit_eq_iff

-- The orbit/coset correspondence and elementary cardinality transport.
#check MulAction.orbitEquivQuotientStabilizer
#check Nat.card_congr
#check Subgroup.index

-- Permutation actions and prime-order elements.
#check MulAction.orbit_eq_univ
#check exists_prime_orderOf_dvd_card

end

/-- **Question 1.** The stabilizer of `x` consists exactly of the group elements that fix `x`. -/
theorem q1_mem_stabilizer_iff (g : G) (x : X) :
    g ∈ MulAction.stabilizer G x ↔ g • x = x := by
  sorry


/-- **Question 2.** Any two orbits of an action are equal or disjoint. -/
theorem q2_orbits_partition (x y : X) : MulAction.orbit G x = MulAction.orbit G y ∨
    Disjoint (MulAction.orbit G x) (MulAction.orbit G y) := by
  sorry


/-- **Question 3.** Orbit–stabilizer: the size of the orbit of `x` is the index of its
stabilizer. -/
theorem q3_orbit_stabilizer [Fintype G] (x : X) :
    Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
  sorry


/-- **Question 4.** The class equation expresses the order of a finite group as the order of its
centre plus the sizes of its noncentral conjugacy classes. -/
theorem q4_class_equation [Finite G] :
    Nat.card (Subgroup.center G) +
      ∑ᶠ (x : ConjClasses G) (_ : x ∈ ConjClasses.noncenter G), Nat.card x.carrier = Nat.card G := by
  sorry


/-- **Question 5.** A nontrivial finite `p`-group has nontrivial centre. -/
theorem q5_pgroup_center_nontrivial {p : ℕ} [Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : Nontrivial (Subgroup.center G) := by
  sorry


/-- **Question 6.** Cauchy's theorem: if a prime divides the order of a finite group, the group
contains an element of that prime order. -/
theorem q6_cauchy {p : ℕ} [Fact p.Prime] [Fintype G] (hp : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p := by
  sorry


/-- **Question 7.** The natural action of `S₃` on three points has a single orbit of size `3`. -/
theorem q7_permutation_orbit :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3)) = 3 := by
  sorry


/-- **Question 8.** Every action of `G` on `X` gives a permutation representation: an element of
`G` acts as a permutation of `X`. -/
theorem q8_permutation_representation :
    ∃ ρ : G →* Equiv.Perm X, ∀ (g : G) (x : X), ρ g x = g • x := by
  sorry

end Exercises.GroupTheory.GroupActions
