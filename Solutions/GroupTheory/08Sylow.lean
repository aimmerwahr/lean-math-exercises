import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic

namespace Solutions.GroupTheory.Sylow

variable {G : Type*} [Group G]


theorem q1_np_one_iff_normal {p : ℕ} [Fact p.Prime] [Finite G] [Finite (Sylow p G)]
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


theorem q2_count_n5_order_15 (n : ℕ) (hmod : n ≡ 1 [MOD 5]) (hdvd : n ∣ 3) : n = 1 := by
  -- The only divisors of the prime 3 are 1 and 3, and 3 has the wrong residue modulo 5.
  have hp : Nat.Prime 3 := by decide
  rcases hp.eq_one_or_self_of_dvd n hdvd with h | h
  · exact h
  · norm_num [h, Nat.ModEq] at hmod


theorem q3_normal_subgroup_order_five [Finite G] (hcard : Nat.card G = 15) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 G := Sylow.nonempty.some
  have hPcard : Nat.card (P : Subgroup G) = 5 := by
    have hfac : (15 : ℕ).factorization 5 = 1 := by
      calc
        (15 : ℕ).factorization 5 = padicValNat 5 15 := Nat.factorization_def _ (by norm_num)
        _ = padicValNat 5 3 + 1 := by
          rw [show (15 : ℕ) = 5 * 3 by norm_num]
          exact padicValNat_base_mul (by norm_num) (by norm_num)
        _ = 1 := by rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [Sylow.card_eq_multiplicity, hcard]
    simp [hfac]
  have hindex : P.index = 3 := by
    have hmul := P.card_mul_index
    rw [hPcard, hcard] at hmul
    omega
  have hnumber : Nat.card (Sylow 5 G) = 1 :=
    q2_count_n5_order_15 _ (card_sylow_modEq_one 5 G) (by simpa [hindex] using P.card_dvd_index)
  exact ⟨P, (q1_np_one_iff_normal P).mp hnumber, hPcard⟩


theorem q4_count_n7_order_21 (n : ℕ) (hmod : n ≡ 1 [MOD 7]) (hdvd : n ∣ 3) : n = 1 := by
  have hp : Nat.Prime 3 := by decide
  rcases hp.eq_one_or_self_of_dvd n hdvd with h | h
  · exact h
  · norm_num [h, Nat.ModEq] at hmod


theorem q5_normal_subgroup_order_seven [Finite G] (hcard : Nat.card G = 21) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let P : Sylow 7 G := Sylow.nonempty.some
  have hPcard : Nat.card (P : Subgroup G) = 7 := by
    have hfac : (21 : ℕ).factorization 7 = 1 := by
      calc
        (21 : ℕ).factorization 7 = padicValNat 7 21 := Nat.factorization_def _ (by norm_num)
        _ = padicValNat 7 3 + 1 := by
          rw [show (21 : ℕ) = 7 * 3 by norm_num]
          exact padicValNat_base_mul (by norm_num) (by norm_num)
        _ = 1 := by rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [Sylow.card_eq_multiplicity, hcard]
    simp [hfac]
  have hindex : P.index = 3 := by
    have hmul := P.card_mul_index
    rw [hPcard, hcard] at hmul
    omega
  have hnumber : Nat.card (Sylow 7 G) = 1 :=
    q4_count_n7_order_21 _ (card_sylow_modEq_one 7 G) (by simpa [hindex] using P.card_dvd_index)
  exact ⟨P, (q1_np_one_iff_normal P).mp hnumber, hPcard⟩


theorem q6_count_n3_order_30 (n : ℕ) (hmod : n ≡ 1 [MOD 3]) (hdvd : n ∣ 10) :
    n = 1 ∨ n = 10 := by
  -- Checking the divisors of 10 against the required residue leaves only 1 and 10.
  have hn : n ≤ 10 := Nat.le_of_dvd (by omega) hdvd
  interval_cases n <;> norm_num [Nat.ModEq] at hmod
  · exact Or.inl rfl
  · exact (by omega : False).elim
  · exact (by omega : False).elim
  · exact Or.inr rfl


theorem q7_normal_subgroup_and_not_simple_order_30 [Finite G] (hcard : Nat.card G = 30) :
    (∃ N : Subgroup G, N.Normal ∧ Nat.card N = 15) ∧ ¬ IsSimpleGroup G := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let P : Sylow 2 G := Sylow.nonempty.some
  have hPcard : Nat.card (P : Subgroup G) = 2 := by
    have hfac : (30 : ℕ).factorization 2 = 1 := by
      calc
        (30 : ℕ).factorization 2 = padicValNat 2 30 := Nat.factorization_def _ (by norm_num)
        _ = padicValNat 2 15 + 1 := by
          rw [show (30 : ℕ) = 2 * 15 by norm_num]
          exact padicValNat_base_mul (by norm_num) (by norm_num)
        _ = 1 := by rw [padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [Sylow.card_eq_multiplicity, hcard]
    simp [hfac]
  have hindex : P.index = 15 := by
    have hmul := P.card_mul_index
    rw [hPcard, hcard] at hmul
    omega
  have hcyclic : IsCyclic P := isCyclic_of_prime_card hPcard
  have hmin : (Nat.card G).minFac = 2 := by
    rw [hcard]
    decide
  let f := MonoidHom.transferSylow P (hcyclic.normalizer_le_centralizer hmin)
  have hNcard : Nat.card f.ker = 15 := by
    rw [← (MonoidHom.ker_transferSylow_isComplement' P
      (hcyclic.normalizer_le_centralizer hmin)).index_eq_card, hindex]
  have hNbot : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hNcard
    omega
  have hNtop : f.ker ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top, hcard] at hNcard
    omega
  constructor
  · exact ⟨f.ker, inferInstance, hNcard⟩
  · intro hsimple
    letI : IsSimpleGroup G := hsimple
    rcases Subgroup.Normal.eq_bot_or_eq_top (inferInstance : f.ker.Normal) with hbot | htop
    · exact hNbot hbot
    · exact hNtop htop

end Solutions.GroupTheory.Sylow
