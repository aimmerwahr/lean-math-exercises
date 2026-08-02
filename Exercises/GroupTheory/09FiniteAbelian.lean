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

#check ZMod.chineseRemainder
#check Nat.Coprime
#check Nat.coprime_comm
#check isAddCyclic_of_addOrderOf_eq_card
#check isAddCyclic_iff_exists_addOrderOf_eq_natCard
#check AddMonoid.exponent_eq_max'_addOrderOf
#check AddEquiv.addOrderOf_eq
#check Nat.cast_smul_eq_nsmul
#check not_isAddCyclic_iff_exponent_eq_prime

end

/-- **Question 1.** If `m` and `n` are coprime, reduction modulo `m` and modulo `n` identifies
`ZMod (m * n)` with `ZMod m × ZMod n`. -/
theorem q1_crt (m n : ℕ) (h : m.Coprime n) : Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) := by
  sorry

/-- **Question 2.** The concrete CRT decomposition `Z/6Z ≅ Z/2Z × Z/3Z`. -/
theorem q2_zmod6_crt : Nonempty (ZMod 6 ≃+* ZMod 2 × ZMod 3) := by
  sorry

/-- **Question 3.** `Z/4Z` is not additively isomorphic to `Z/2Z × Z/2Z`: every element of the
latter is killed by two, whereas `1 : Z/4Z` is not. -/
theorem q3_zmod4_not_prod : ¬ Nonempty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  sorry

/-- **Question 4.** The order of an element in a direct product is the least common multiple of
the orders of its two coordinates. -/
theorem q4_prod_order {G H : Type*} [CommGroup G] [CommGroup H] (a : G) (b : H) :
    orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b) := by
  sorry

/-- **Question 5.** The three familiar abelian group models for groups of order eight all have
the claimed cardinality.  The classification theorem distinguishes their structures further. -/
theorem q5_order_eight_models :
    Nat.card (ZMod 8) = 8 ∧ Nat.card (ZMod 4 × ZMod 2) = 8 ∧
      Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
  sorry

/-- **Question 6.** A finite abelian group is cyclic exactly when one of its elements has order
equal to the cardinality of the group. -/
theorem q6_cyclic_iff_full_order {G : Type*} [AddCommGroup G] [Fintype G] :
    IsAddCyclic G ↔ ∃ g : G, addOrderOf g = Nat.card G := by
  sorry

/-- **Question 7.** In a finite abelian group, some element realizes the exponent. -/
theorem q7_exponent_attained {G : Type*} [AddCommGroup G] [Fintype G] :
    ∃ g : G, addOrderOf g = AddMonoid.exponent G := by
  sorry

/-- **Question 8.** The order-`p²` case has the expected cyclic/noncyclic dichotomy: a
noncyclic abelian group has exponent `p`. -/
theorem q8_not_cyclic_iff_exponent_prime {G : Type*} [AddCommGroup G] {p : ℕ}
    (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    ¬ IsAddCyclic G ↔ AddMonoid.exponent G = p := by
  sorry

/-- **Question 9.** The three standard abelian groups of order eight are pairwise
non-isomorphic.  Distinguish them by the orders of their elements. -/
theorem q9_order_eight_pairwise_not_equiv :
    ¬ Nonempty (ZMod 8 ≃+ ZMod 4 × ZMod 2) ∧
      ¬ Nonempty (ZMod 8 ≃+ ZMod 2 × ZMod 2 × ZMod 2) ∧
        ¬ Nonempty (ZMod 4 × ZMod 2 ≃+ ZMod 2 × ZMod 2 × ZMod 2) := by
  sorry

end Exercises.GroupTheory.FiniteAbelian
