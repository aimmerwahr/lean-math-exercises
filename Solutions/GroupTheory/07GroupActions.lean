import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Solutions.GroupTheory.GroupActions

variable {G X : Type*} [Group G] [MulAction G X]

theorem q1_mem_stabilizer_iff (g : G) (x : X) :
    g ∈ MulAction.stabilizer G x ↔ g • x = x := by
  rfl

theorem q2_orbits_partition (x y : X) : MulAction.orbit G x = MulAction.orbit G y ∨
    Disjoint (MulAction.orbit G x) (MulAction.orbit G y) := by
  by_cases h : x ∈ MulAction.orbit G y
  · exact Or.inl (MulAction.orbit_eq_iff.mpr h)
  · right
    rw [Set.disjoint_left]
    intro z hzx hzy
    -- A point reached from both x and y transports x into the orbit of y, contradicting h.
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hzx
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hzy
    apply h
    refine MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * k, ?_⟩
    rw [mul_smul, hk, ← hg]
    simp

theorem q3_orbit_stabilizer [Fintype G] (x : X) :
    Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
  -- The orbit is in bijection with the left cosets of the stabilizer, so their cardinalities agree.
  rw [Subgroup.index]
  exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)

theorem q4_class_equation [Finite G] :
    Nat.card (Subgroup.center G) +
      ∑ᶠ (x : ConjClasses G) (_ : x ∈ ConjClasses.noncenter G), Nat.card x.carrier = Nat.card G := by
  -- Conjugation partitions G into its central singleton classes and its noncentral classes.
  exact Group.nat_card_center_add_sum_card_noncenter_eq_card G

theorem q5_pgroup_center_nontrivial {p : ℕ} [Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : Nontrivial (Subgroup.center G) := by
  -- In a finite p-group, the class equation leaves a nonidentity element in the centre.
  exact IsPGroup.center_nontrivial hG

theorem q6_cauchy {p : ℕ} [Fact p.Prime] [Fintype G] (hp : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p := by
  -- Prime divisibility of the group order forces a cyclic subgroup of that prime order.
  exact exists_prime_orderOf_dvd_card p hp

theorem q7_permutation_orbit :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3)) = 3 := by
  -- Any point of a three-element set can be sent to any other by a permutation.
  rw [MulAction.orbit_eq_univ]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.Set.univ (Fin 3))

theorem q8_permutation_representation :
    ∃ ρ : G →* Equiv.Perm X, ∀ (g : G) (x : X), ρ g x = g • x := by
  -- The action maps each group element to the permutation it induces on X.
  exact ⟨MulAction.toPermHom G X, fun _ _ => rfl⟩

end Solutions.GroupTheory.GroupActions
