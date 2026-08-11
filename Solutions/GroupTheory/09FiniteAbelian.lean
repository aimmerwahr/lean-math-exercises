import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Solutions.GroupTheory.FiniteAbelian

theorem q1_zmod4_not_prod : ¬ Nonempty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  -- Doubling any pair of residues mod 2 gives zero.
  rintro ⟨e⟩
  have h : e (1 : ZMod 4) + e (1 : ZMod 4) = 0 := by
    obtain ⟨a, b⟩ := e (1 : ZMod 4)
    change (a + a, b + b) = (0, 0)
    rw [← two_nsmul, ← two_nsmul]
    ext
    · exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (by simpa using addOrderOf_dvd_card (x := a))
    · exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (by simpa using addOrderOf_dvd_card (x := b))
  have h' : (1 : ZMod 4) + 1 = 0 := by
    simpa using congrArg e.symm h
  have hdiv : addOrderOf (1 : ZMod 4) ∣ 2 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    simpa only [two_nsmul] using h'
  rw [ZMod.addOrderOf_one] at hdiv
  norm_num at hdiv


theorem q2_order_zmod4_prod : addOrderOf ((1, 0) : ZMod 4 × ZMod 2) = 4 := by
  norm_num [Prod.addOrderOf_mk, ZMod.addOrderOf_one]


theorem q3_order_eight_models :
    Nat.card (ZMod 8) = 8 ∧ Nat.card (ZMod 4 × ZMod 2) = 8 ∧
      Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
  -- Cardinalities multiply in a direct product.
  norm_num [Nat.card_prod, Nat.card_zmod]


theorem q4_zmod8_cyclic : IsAddCyclic (ZMod 8) := by
  apply isAddCyclic_of_addOrderOf_eq_card (x := (1 : ZMod 8))
  rw [ZMod.addOrderOf_one]
  norm_num [Nat.card_zmod]


theorem q5_exponent_attained {G : Type*} [AddCommGroup G] [Fintype G] :
    ∃ g : G, addOrderOf g = AddMonoid.exponent G := by
  -- In a finite group the largest element order occurs; commutativity identifies that maximum
  -- with the exponent.
  classical
  let orders := (Finset.univ : Finset G).image addOrderOf
  have horders : orders.Nonempty := by simp [orders]
  obtain ⟨g, -, hg⟩ := Finset.mem_image.mp (Finset.max'_mem orders horders)
  exact ⟨g, hg.trans AddMonoid.exponent_eq_max'_addOrderOf.symm⟩


theorem q6_two_smul_triple_zero (x : ZMod 2 × ZMod 2 × ZMod 2) : (2 : ℕ) • x = 0 := by
  have two_smul_zero (a : ZMod 2) : (2 : ℕ) • a = 0 := by
    have htwo : (2 : ZMod 2) = 0 := by
      change ((2 : ℕ) : ZMod 2) = 0
      rw [ZMod.natCast_eq_zero_iff]
    calc
      (2 : ℕ) • a = (2 : ZMod 2) • a := (Nat.cast_smul_eq_nsmul (ZMod 2) 2 a).symm
      _ = 0 := by rw [htwo, zero_smul]
  rcases x with ⟨a, b, c⟩
  change ((2 : ℕ) • a, (2 : ℕ) • b, (2 : ℕ) • c) = (0, 0, 0)
  ext <;> apply two_smul_zero


theorem q7_order_eight_pairwise_not_equiv :
    ¬ Nonempty (ZMod 8 ≃+ ZMod 4 × ZMod 2) ∧
      ¬ Nonempty (ZMod 8 ≃+ ZMod 2 × ZMod 2 × ZMod 2) ∧
        ¬ Nonempty (ZMod 4 × ZMod 2 ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by
  have kill_four : ∀ x : ZMod 4 × ZMod 2, (4 : ℕ) • x = 0 := by
    rintro ⟨a, b⟩
    change ((4 : ℕ) • a, (4 : ℕ) • b) = (0, 0)
    ext
    · exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (by simpa using addOrderOf_dvd_card (x := a))
    · apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      have hb : addOrderOf b ∣ 2 := by simpa using addOrderOf_dvd_card (x := b)
      exact hb.trans (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have hdiv : addOrderOf (1 : ZMod 8) ∣ 4 := by
      rw [← e.addOrderOf_eq]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (kill_four (e 1))
    rw [ZMod.addOrderOf_one] at hdiv
    norm_num at hdiv
  · rintro ⟨e⟩
    have hdiv : addOrderOf (1 : ZMod 8) ∣ 2 := by
      rw [← e.addOrderOf_eq]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (q6_two_smul_triple_zero (e 1))
    rw [ZMod.addOrderOf_one] at hdiv
    norm_num at hdiv
  · rintro ⟨e⟩
    have hdiv : addOrderOf ((1, 0) : ZMod 4 × ZMod 2) ∣ 2 := by
      rw [← e.addOrderOf_eq]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (q6_two_smul_triple_zero (e (1, 0)))
    rw [q2_order_zmod4_prod] at hdiv
    norm_num at hdiv

end Solutions.GroupTheory.FiniteAbelian
