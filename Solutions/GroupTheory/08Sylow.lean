import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace Solutions.GroupTheory.Sylow

variable {G : Type*} [Group G]

theorem q1_sylow_exists {p n : ℕ} [Fact p.Prime] [Finite G] (hpow : p ^ n ∣ Nat.card G) :
    ∃ K : Subgroup G, Nat.card K = p ^ n := by
  -- A maximal p-subgroup exists for every p-power already present in the group order.
  exact Sylow.exists_subgroup_card_pow_prime p hpow


theorem q2_card_sylow_mod_p {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  -- Conjugation of Sylow subgroups leaves precisely one fixed subgroup modulo p.
  exact card_sylow_modEq_one p G


theorem q3_np_one_iff_normal {p : ℕ} [Fact p.Prime] [Finite G] [Fintype (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = 1 ↔ (P : Subgroup G).Normal := by
  constructor
  · intro hcard
    -- One Sylow subgroup has no conjugates other than itself, so it is invariant under conjugation.
    have hsub : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hcard).1
    letI : Subsingleton (Sylow p G) := hsub
    exact Sylow.normal_of_subsingleton P
  · intro hnormal
    -- Normality makes every conjugate of P equal to P, hence P is the sole Sylow subgroup.
    letI : Unique (Sylow p G) := Sylow.unique_of_normal P hnormal
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩


theorem q4_count_n5_order_15 (n : ℕ) (hmod : n ≡ 1 [MOD 5]) (hdvd : n ∣ 3) : n = 1 := by
  -- The only divisors of the prime 3 are 1 and 3, and 3 has the wrong residue modulo 5.
  have hp : Nat.Prime 3 := by decide
  rcases hp.eq_one_or_self_of_dvd n hdvd with h | h
  · exact h
  · norm_num [h, Nat.ModEq] at hmod


theorem q5_count_n3_order_30 (n : ℕ) (hmod : n ≡ 1 [MOD 3]) (hdvd : n ∣ 10) :
    n = 1 ∨ n = 10 := by
  -- Checking the divisors of 10 against the required residue leaves only 1 and 10.
  have hn : n ≤ 10 := Nat.le_of_dvd (by omega) hdvd
  interval_cases n <;> norm_num [Nat.ModEq] at hmod
  · exact Or.inl rfl
  · exact (by omega : False).elim
  · exact (by omega : False).elim
  · exact Or.inr rfl


theorem q6_sylow_order {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p ^ (Nat.card G).factorization p := by
  -- By definition, a Sylow subgroup captures the entire p-part of the group order.
  exact Sylow.card_eq_multiplicity P

end Solutions.GroupTheory.Sylow
