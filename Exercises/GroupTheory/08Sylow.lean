import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Sylow Theory

Sylow theory measures the part of a finite group controlled by a prime `p`. A Sylow
`p`-subgroup has the largest possible power of `p` in its order. The three Sylow theorems give
existence, conjugacy, and tight arithmetic restrictions on the number of such subgroups. Those
restrictions are powerful: a count equal to one makes the Sylow subgroup normal, and simple
divisibility and congruence arguments can force that outcome in concrete group orders.

Prove each statement yourself; canonical proofs live in `Solutions/GroupTheory/08Sylow.lean`.
Do not commit proofs into this file.
-/

namespace Exercises.GroupTheory.Sylow

variable {G : Type*} [Group G]

/-! ## Potentially helpful results -/
section

-- Existence and size of maximal p-subgroups.
#check Sylow.exists_subgroup_card_pow_prime
#check Sylow.card_eq_multiplicity

-- Counting Sylow subgroups and recognizing uniqueness.
#check card_sylow_modEq_one
#check Sylow.unique_of_normal
#check Sylow.normal_of_subsingleton
#check Nat.card_eq_one_iff_unique

-- Elementary arithmetic for concrete Sylow counts.
#check Nat.Prime.eq_one_or_self_of_dvd
#check Nat.le_of_dvd

end

/-- **Question 1.** If `p^n` divides the order of a finite group, the group has a subgroup of
order `p^n`. -/
theorem q1_sylow_exists {p n : ℕ} [Fact p.Prime] [Finite G] (hpow : p ^ n ∣ Nat.card G) :
    ∃ K : Subgroup G, Nat.card K = p ^ n := by
  sorry


/-- **Question 2.** The number of Sylow `p`-subgroups is congruent to `1` modulo `p`. -/
theorem q2_card_sylow_mod_p {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  sorry


/-- **Question 3.** A Sylow `p`-subgroup is normal exactly when it is the unique Sylow
`p`-subgroup. -/
theorem q3_np_one_iff_normal {p : ℕ} [Fact p.Prime] [Finite G] [Fintype (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = 1 ↔ (P : Subgroup G).Normal := by
  sorry


/-- **Question 4.** A positive integer dividing `3` and congruent to `1` modulo `5` is `1`.
This is the Sylow count calculation for the number of Sylow `5`-subgroups in a group of order
`15`. -/
theorem q4_count_n5_order_15 (n : ℕ) (hmod : n ≡ 1 [MOD 5]) (hdvd : n ∣ 3) : n = 1 := by
  sorry


/-- **Question 5.** A positive integer dividing `10` and congruent to `1` modulo `3` is either
`1` or `10`. This is the corresponding first restriction on the number of Sylow `3`-subgroups in
a group of order `30`. -/
theorem q5_count_n3_order_30 (n : ℕ) (hmod : n ≡ 1 [MOD 3]) (hdvd : n ∣ 10) :
    n = 1 ∨ n = 10 := by
  sorry


/-- **Question 6.** A Sylow `p`-subgroup has order equal to the largest power of `p` dividing the
order of the group. -/
theorem q6_sylow_order {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p ^ (Nat.card G).factorization p := by
  sorry

end Exercises.GroupTheory.Sylow
