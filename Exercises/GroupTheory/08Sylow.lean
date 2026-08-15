import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Sylow Theory

Sylow theory measures the part of a finite group controlled by a prime `p`. A Sylow
`p`-subgroup has the largest possible power of `p` in its order. The three Sylow theorems give
existence, conjugacy, and tight arithmetic restrictions on the number of such subgroups. Those
restrictions are powerful: a count equal to one makes the Sylow subgroup normal, and simple
divisibility and congruence arguments can force that outcome in concrete group orders. When a
counting argument alone does not decide the issue, a normal-complement theorem can provide a
further route to a proper normal subgroup.

Prove each statement yourself; canonical proofs live in `Solutions/GroupTheory/08Sylow.lean`.
Do not commit proofs into this file.
-/

namespace Exercises.GroupTheory.Sylow

variable {G : Type*} [Group G]

/-! ## Potentially helpful results -/
section

-- Existence and size of maximal p-subgroups.
#check @Sylow.exists_subgroup_card_pow_prime
#check @Sylow.card_eq_multiplicity

-- Counting Sylow subgroups and recognizing uniqueness.
#check @card_sylow_modEq_one
#check @Sylow.unique_of_normal
#check @Sylow.normal_of_subsingleton
#check @Nat.card_eq_one_iff_unique

-- Elementary arithmetic for concrete Sylow counts.
#check @Nat.Prime.eq_one_or_self_of_dvd
#check @Nat.le_of_dvd

-- A cyclic Sylow subgroup for the smallest prime divisor has a normal complement.
#check @isCyclic_of_prime_card
#check @IsCyclic.isComplement'

end


/-- **Question 1.**

A Sylow `p`-subgroup is normal exactly when it is the unique Sylow
`p`-subgroup. -/
theorem q1_np_one_iff_normal {p : ℕ} [Fact p.Prime] [Finite G] [Finite (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = 1 ↔ (P : Subgroup G).Normal := by
  sorry


/-- **Question 2.**

A positive integer dividing `3` and congruent to `1` modulo `5` is `1`.
This is the count calculation for the Sylow `5`-subgroups of a group of order `15`. -/
theorem q2_count_n5_order_15 (n : ℕ) (hmod : n ≡ 1 [MOD 5]) (hdvd : n ∣ 3) : n = 1 := by
  sorry


/-- **Question 3.**

Every group of order `15` has a normal subgroup of order `5`.

Choose a Sylow `5`-subgroup. Its order determines that its index is `3`; use the Sylow count
congruence and Question 2 to show it is unique. -/
theorem q3_normal_subgroup_order_five [Finite G] (hcard : Nat.card G = 15) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 5 := by
  sorry


/-- **Question 4.**

A positive integer dividing `3` and congruent to `1` modulo `7` is `1`.
This is the count calculation for the Sylow `7`-subgroups of a group of order `21`. -/
theorem q4_count_n7_order_21 (n : ℕ) (hmod : n ≡ 1 [MOD 7]) (hdvd : n ∣ 3) : n = 1 := by
  sorry


/-- **Question 5.**

Every group of order `21` has a normal subgroup of order `7`.

Follow the same chain of implications as in Question 3, now using Question 4. -/
theorem q5_normal_subgroup_order_seven [Finite G] (hcard : Nat.card G = 21) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7 := by
  sorry


/-- **Question 6.**

A positive integer dividing `10` and congruent to `1` modulo `3` is either
`1` or `10`. This is the corresponding first restriction on the number of Sylow `3`-subgroups in
a group of order `30`. -/
theorem q6_count_n3_order_30 (n : ℕ) (hmod : n ≡ 1 [MOD 3]) (hdvd : n ∣ 10) :
    n = 1 ∨ n = 10 := by
  sorry


/-- **Question 7.**

Every group of order `30` has a proper nontrivial normal subgroup, and hence is not simple.

A Sylow `2`-subgroup has order `2`, so it is cyclic. Since `2` is the smallest prime divisor of
`30`, apply the normal-complement theorem to obtain a normal subgroup of order `15`. -/
theorem q7_normal_subgroup_and_not_simple_order_30 [Finite G] (hcard : Nat.card G = 30) :
    (∃ N : Subgroup G, N.Normal ∧ Nat.card N = 15) ∧ ¬ IsSimpleGroup G := by
  sorry

end Exercises.GroupTheory.Sylow
