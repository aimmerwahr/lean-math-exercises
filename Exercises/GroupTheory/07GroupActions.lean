import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
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
#check @MulAction.mem_orbit
#check @MulAction.mem_orbit_iff
#check @MulAction.mem_orbit_symm
#check @MulAction.orbit_eq_iff

-- The orbit/coset correspondence and elementary cardinality transport.
#check @MulAction.orbitEquivQuotientStabilizer
#check @Nat.card_congr
#check @Subgroup.index

-- Permutation actions and prime-order elements.
#check @MulAction.orbit_eq_univ
#check @IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
#check @ConjAct.fixedPoints_eq_center
#check @MulAction.toPerm

end


/-- **Question 1.**

The stabilizer of `x` consists exactly of the group elements that fix `x`. -/
theorem q1_mem_stabilizer_iff (g : G) (x : X) :
    g ∈ MulAction.stabilizer G x ↔ g • x = x := by
  sorry


/-- **Question 2.**

Any two orbits of an action are equal or disjoint. -/
theorem q2_orbits_partition (x y : X) : MulAction.orbit G x = MulAction.orbit G y ∨
    Disjoint (MulAction.orbit G x) (MulAction.orbit G y) := by
  sorry


/-- **Question 3.**

Orbit–stabilizer: the size of the orbit of `x` is the index of its
stabilizer. -/
theorem q3_orbit_stabilizer [Fintype G] (x : X) :
    Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
  sorry


/-- **Question 4.**

The first step of the class equation: conjugacy classes partition a group.
The sigma type on the left records an element together with its conjugacy class.

Prove without using `Group.sum_card_conj_classes_eq_card` or
`Group.nat_card_center_add_sum_card_noncenter_eq_card`. -/
theorem q4_conjugacy_classes_partition :
    Nat.card (Σ x : ConjClasses G, x.carrier) = Nat.card G := by
  sorry


/-- **Question 5.**

A nontrivial finite `p`-group has nontrivial centre.

Prove without using `IsPGroup.center_nontrivial`. -/
theorem q5_pgroup_center_nontrivial {p : ℕ} [Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : Nontrivial (Subgroup.center G) := by
  sorry


/-- **Question 6.**

The product `(0\;1)(1\;2)` in `S₃` has order `3`. This is a concrete
instance of the phenomenon behind Cauchy's theorem. -/
theorem q6_three_cycle_order :
    orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 3 := by
  sorry


/-- **Question 7.**

The natural action of `S₃` on three points has a single orbit of size `3`. -/
theorem q7_permutation_orbit :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3)) = 3 := by
  sorry


/-- **Question 8.**

Every action of `G` gives a permutation representation: construct the
homomorphism which sends `g` to the permutation `x ↦ g • x`.

Prove without using `MulAction.toPermHom`. -/
theorem q8_permutation_representation :
    ∃ ρ : G →* Equiv.Perm X, ∀ (g : G) (x : X), ρ g x = g • x := by
  sorry


/-- **Question 9.**

A permutation is an **involution** if applying it twice is the identity.
Show that inversion is an involution of a group. -/
theorem q9_inversion_is_involution (x : G) : (x⁻¹)⁻¹ = x := by
  sorry


/-- **Question 10.**

The fixed points of inversion are exactly the solutions of `x² = 1`.
They are not usually a subgroup: in a non-abelian group, products of involutions need not be
involutions. -/
theorem q10_inversion_fixed_iff (x : G) : x⁻¹ = x ↔ x * x = 1 := by
  sorry


/-- **Question 11.**

An involution partitions a finite set into fixed points and two-element orbits. Therefore its
fixed-point set has the same parity as the whole set. Apply this to inversion: a finite group of
even order has a nonidentity element `x` with `x² = 1`.

Prove without using `exists_prime_orderOf_dvd_card`. -/
theorem q11_even_order_involution [Fintype G] [DecidableEq G]
    (h : 2 ∣ Fintype.card G) : ∃ x : G, x ≠ 1 ∧ x * x = 1 := by
  sorry

end Exercises.GroupTheory.GroupActions
