import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Solutions.GroupTheory.GroupActions

variable {G X : Type*} [Group G] [MulAction G X]

open MulAction ConjClasses

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


theorem q4_conjugacy_classes_partition :
    Nat.card (Σ x : ConjClasses G, x.carrier) = Nat.card G := by
  apply Nat.card_congr
  simpa [carrier_eq_preimage_mk] using! Equiv.sigmaFiberEquiv ConjClasses.mk


theorem q5_pgroup_center_nontrivial {p : ℕ} [Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : Nontrivial (Subgroup.center G) := by
  have hfixed := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixedPoints_eq_center] at hfixed
  have hdvd : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨g, hg⟩ := hfixed hdvd (Subgroup.center G).one_mem
  exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩


private def q6ThreeCycle : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

theorem q6_three_cycle_order : orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) = 3 := by
  change orderOf q6ThreeCycle = 3
  refine (orderOf_eq_iff (by norm_num)).mpr ⟨?_, ?_⟩
  · ext i
    fin_cases i <;> rfl
  · intro m hm hm0
    interval_cases m <;> try omega
    · intro h
      have he := DFunLike.congr_fun h (0 : Fin 3)
      have hmove : (q6ThreeCycle ^ 1) 0 = 1 := by rfl
      rw [hmove] at he
      norm_num at he
    · intro h
      have he := DFunLike.congr_fun h (0 : Fin 3)
      have hmove : (q6ThreeCycle ^ 2) 0 = 2 := by rfl
      rw [hmove] at he
      exact (by decide : (2 : Fin 3) ≠ 0) he


theorem q7_permutation_orbit :
    Nat.card (MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3)) = 3 := by
  have horbit : MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine MulAction.mem_orbit_iff.mpr ⟨Equiv.swap 0 x, ?_⟩
    simp
  rw [horbit]
  rw [Nat.card_eq_fintype_card]
  rfl


theorem q8_permutation_representation :
    ∃ ρ : G →* Equiv.Perm X, ∀ (g : G) (x : X), ρ g x = g • x := by
  let ρ : G →* Equiv.Perm X :=
    { toFun := MulAction.toPerm
      map_one' := by
        ext x
        exact one_smul G x
      map_mul' := by
        intro g h
        ext x
        exact mul_smul g h x }
  exact ⟨ρ, fun _ _ => rfl⟩


theorem q9_inversion_is_involution (x : G) : (x⁻¹)⁻¹ = x := inv_inv x


theorem q10_inversion_fixed_iff (x : G) : x⁻¹ = x ↔ x * x = 1 := by
  constructor
  · intro h
    exact mul_eq_one_iff_eq_inv.mpr h.symm
  · exact fun h => (mul_eq_one_iff_eq_inv.mp h).symm


theorem q11_even_order_involution [Fintype G] [DecidableEq G]
    (h : 2 ∣ Fintype.card G) : ∃ x : G, x ≠ 1 ∧ x * x = 1 := by
  -- The preceding questions identify the fixed points. The remaining counting fact is the orbit
  -- decomposition of an involution: every non-fixed orbit has two elements.
  let f : Function.End G := fun x => x⁻¹
  have hf : f ^ (2 ^ 1) = 1 := by
    show f ^ 2 = 1
    rw [pow_two]
    show f ∘ f = id
    funext x
    simp [f]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := G) (f := f) (p := 2) (n := 1) hf
  have hdvd : 2 ∣ Fintype.card f.fixedPoints := by
    have h0 : Fintype.card G ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr h
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans h0)
  have h1mem : (1 : G) ∈ f.fixedPoints := by
    show (1 : G)⁻¹ = 1
    simp
  have hpos : 0 < Fintype.card f.fixedPoints := Fintype.card_pos_iff.mpr ⟨⟨1, h1mem⟩⟩
  have hle : 2 ≤ Fintype.card f.fixedPoints := Nat.le_of_dvd hpos hdvd
  obtain ⟨b, hb⟩ :=
    Fintype.exists_ne_of_one_lt_card (lt_of_lt_of_le one_lt_two hle) (⟨1, h1mem⟩ : f.fixedPoints)
  refine ⟨b.1, ?_, ?_⟩
  · intro hb1
    exact hb (Subtype.ext hb1)
  · exact (q10_inversion_fixed_iff b.1).mp b.2

end Solutions.GroupTheory.GroupActions
