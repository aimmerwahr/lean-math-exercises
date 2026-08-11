import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Finite Abelian Groups

Finite abelian groups are assembled from cyclic groups.  The Chinese remainder theorem is the
basic concrete construction: coprime moduli split into independent modular coordinates.
The full classification theorem says that this phenomenon, iterated through prime powers,
accounts for every finite abelian group.

Prove each statement yourself; canonical proofs live in `Solutions/GroupTheory/09FiniteAbelian.lean`.
-/

namespace Exercises.GroupTheory.FiniteAbelian

/-! ## Potentially helpful results -/
section

#check isAddCyclic_of_addOrderOf_eq_card
#check isAddCyclic_iff_exists_addOrderOf_eq_natCard
#check AddMonoid.exponent_eq_max'_addOrderOf
#check AddEquiv.addOrderOf_eq
#check Nat.cast_smul_eq_nsmul
end

/-- **Question 1.** `Z/4Z` is not additively isomorphic to `Z/2Z × Z/2Z`: every element of the
latter is killed by two, whereas `1 : Z/4Z` is not. -/
theorem q1_zmod4_not_prod : ¬ Nonempty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  sorry


/-- **Question 2.** The element `(1, 0)` in `Z/4Z × Z/2Z` has additive order `4`. -/
theorem q2_order_zmod4_prod : addOrderOf ((1, 0) : ZMod 4 × ZMod 2) = 4 := by
  sorry


/-- **Question 3.** The three familiar abelian group models for groups of order eight all have
the claimed cardinality.  The classification theorem distinguishes their structures further. -/
theorem q3_order_eight_models :
    Nat.card (ZMod 8) = 8 ∧ Nat.card (ZMod 4 × ZMod 2) = 8 ∧
      Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
  sorry


/-- **Question 4.** `Z/8Z` is cyclic: exhibit a generator by checking that `1` has additive
order eight. -/
theorem q4_zmod8_cyclic : IsAddCyclic (ZMod 8) := by
  sorry


/-- **Question 5.** In a finite abelian group, some element realizes the exponent. -/
theorem q5_exponent_attained {G : Type*} [AddCommGroup G] [Fintype G] :
    ∃ g : G, addOrderOf g = AddMonoid.exponent G := by
  sorry


/-- **Question 6.** Every element of `Z/2Z × Z/2Z × Z/2Z` is killed by two. This is the
order obstruction that distinguishes it from the other groups of order eight. -/
theorem q6_two_smul_triple_zero (x : ZMod 2 × ZMod 2 × ZMod 2) : (2 : ℕ) • x = 0 := by
  sorry


/-- **Question 7.** The three standard abelian groups of order eight are pairwise
non-isomorphic.  Distinguish them by the orders of their elements. -/
theorem q7_order_eight_pairwise_not_equiv :
    ¬ Nonempty (ZMod 8 ≃+ ZMod 4 × ZMod 2) ∧
      ¬ Nonempty (ZMod 8 ≃+ ZMod 2 × ZMod 2 × ZMod 2) ∧
        ¬ Nonempty (ZMod 4 × ZMod 2 ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by
  sorry

end Exercises.GroupTheory.FiniteAbelian
