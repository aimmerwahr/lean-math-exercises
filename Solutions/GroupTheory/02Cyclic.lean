import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

namespace Solutions.GroupTheory.Cyclic

open Subgroup

variable {G : Type*} [Group G]

theorem q1_powerOf_pow_eq_one_iff [Finite G] (g : G) (k m : ℕ) :
    (g ^ k) ^ m = 1 ↔ orderOf g ∣ k * m := by
  rw [← pow_mul, orderOf_dvd_iff_pow_eq_one]

theorem q2_orderOf_pow [Finite G] (g : G) (k : ℕ) :
    orderOf (g ^ k) = orderOf g / (orderOf g).gcd k := by
  -- Write `n = orderOf g` and `d = gcd n k`, so `n = d·n'`, `k = d·k'` with `n'`, `k'` coprime.
  set n := orderOf g with hn
  set d := n.gcd k with hd
  have hn0 : 0 < n := orderOf_pos g
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left k hn0
  have hdn : d ∣ n := Nat.gcd_dvd_left n k
  have hdk : d ∣ k := Nat.gcd_dvd_right n k
  have hcop0 : Nat.Coprime (n / d) (k / d) := Nat.coprime_div_gcd_div_gcd hd0
  clear_value d n
  obtain ⟨n', hn'⟩ := hdn
  obtain ⟨k', hk'⟩ := hdk
  have hnd : n / d = n' := by rw [hn']; exact Nat.mul_div_cancel_left n' hd0
  have hkd : k / d = k' := by rw [hk']; exact Nat.mul_div_cancel_left k' hd0
  rw [hnd, hkd] at hcop0
  rw [hnd]
  -- The order of `gᵏ` is exactly `n' = n / d`: it divides `n'`, and `n'` divides it.
  apply Nat.dvd_antisymm
  · -- `(gᵏ)^{n'} = g^{k·n'} = g^{k'·n} = (gⁿ)^{k'} = 1`.
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul]
    have hexp : k * n' = n * k' := by rw [hk', hn']; ring
    rw [hexp, pow_mul, hn, pow_orderOf_eq_one, one_pow]
  · -- If `(gᵏ)^m = 1` then `n ∣ k·m`, so `n' ∣ k'·m`; as `n'`, `k'` are coprime, `n' ∣ m`.
    have h1 : g ^ (k * orderOf (g ^ k)) = 1 := by
      rw [pow_mul]; exact pow_orderOf_eq_one _
    have h2 : n ∣ k * orderOf (g ^ k) := by
      rw [hn]; exact orderOf_dvd_of_pow_eq_one h1
    rw [hn'] at h2
    nth_rewrite 1 [hk'] at h2
    rw [mul_assoc] at h2
    have h3 : n' ∣ k' * orderOf (g ^ k) :=
      (mul_dvd_mul_iff_left (show (d : ℕ) ≠ 0 from hd0.ne')).mp h2
    exact hcop0.dvd_of_dvd_mul_left h3


theorem q3_generator_iff_coprime [Finite G] (g : G) (k : ℕ) :
    orderOf (g ^ k) = orderOf g ↔ Nat.Coprime (orderOf g) k := by
  -- `gᵏ` has the same order as `g` (so it generates the same cyclic group) exactly when
  -- `n / gcd(n, k) = n`, i.e. when `gcd(n, k) = 1`.
  rw [q2_orderOf_pow g k, Nat.div_eq_self]
  constructor
  · rintro (h | h)
    · exact absurd h (orderOf_pos g).ne'
    · exact h
  · intro h; exact Or.inr h


theorem q4_generators_zmod :
    Finset.univ.filter (fun a : ZMod 12 => Nat.Coprime a.val 12) = {1, 5, 7, 11} := by
  -- A residue generates the additive group `ℤ/12` iff it is coprime to `12`; the coprime residues
  -- below `12` are `1, 5, 7, 11`.
  decide


theorem q5_subgroup_isCyclic [IsCyclic G] (H : Subgroup G) : IsCyclic H := by
  -- Pick a generator `g` of `G`. If `H` is trivial it is cyclic. Otherwise let `m` be the least
  -- positive exponent with `gᵐ ∈ H`; then `gᵐ` generates `H`: divide any exponent `k` by `m`, and
  -- minimality forces the remainder to vanish, so every element of `H` is a power of `gᵐ`.
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  by_cases hx : ∃ x : G, x ∈ H ∧ x ≠ (1 : G)
  · obtain ⟨x, hx₁, hx₂⟩ := hx
    obtain ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
      refine ⟨k.natAbs, Nat.pos_of_ne_zero fun h => hx₂ ?_, ?_⟩
      · rw [← hk, Int.natAbs_eq_zero.mp h, zpow_zero]
      · rcases k with k | k
        · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
            ← Int.ofNat_eq_natCast, hk]
          exact hx₁
        · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all
    refine ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hk₂ : g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) ∈ H := by
      rw [zpow_mul]; apply H.zpow_mem; exact mod_cast (Nat.find_spec hex).2
    have hk₃ : g ^ (k % Nat.find hex : ℤ) ∈ H :=
      (Subgroup.mul_mem_cancel_right H hk₂).1 <| by
        rw [← zpow_add, Int.emod_add_mul_ediv, hk]; exact hx
    have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs :=
      (Int.natAbs_of_nonneg
        (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))).symm
    have hk₅ : g ^ (k % Nat.find hex).natAbs ∈ H := by rwa [← zpow_natCast, ← hk₄]
    have hk₆ : (k % (Nat.find hex : ℤ)).natAbs = 0 :=
      by_contradiction fun h =>
        Nat.find_min hex
          (Int.ofNat_lt.1 <| by
            rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
          ⟨Nat.pos_of_ne_zero h, hk₅⟩
    refine ⟨k / (Nat.find hex : ℤ), Subtype.ext_iff.2 ?_⟩
    suffices g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) = x by simpa [zpow_mul]
    rw [Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆)), hk]
  · have hbot : H = (⊥ : Subgroup G) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp only [Subgroup.mem_bot]; by_contra hne; exact hx ⟨x, h, hne⟩,
         fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    rw [hbot]; exact Bot.isCyclic


theorem q6_unique_subgroup_per_divisor [Finite G] [IsCyclic G] {d : ℕ}
    (hd : d ∣ Nat.card G) : ∃! H : Subgroup G, Nat.card H = d := by
  -- Fix a generator `g`, so `orderOf g = |G| =: N`. Bézout shows `g^{gcd(N,k)}` is a power of
  -- `g^k`; from this every subgroup is `zpowers (g^{N/|H|})`. That single description yields both a
  -- subgroup of each order `d ∣ N` and its uniqueness.
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hNpos : 0 < Nat.card G := Nat.card_pos
  have hgn : g ^ (Nat.card G : ℤ) = 1 := by rw [← hgord, zpow_natCast, pow_orderOf_eq_one]
  -- Bézout: `g^{gcd(N,k)}` lies in the group generated by `g^k`.
  have hbez : ∀ k : ℕ, g ^ Nat.gcd (Nat.card G) k ∈ Subgroup.zpowers (g ^ k) := by
    intro k
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨Nat.gcdB (Nat.card G) k, ?_⟩
    have hbz : ((Nat.gcd (Nat.card G) k : ℤ))
        = Nat.card G * Nat.gcdA (Nat.card G) k + k * Nat.gcdB (Nat.card G) k :=
      Nat.gcd_eq_gcd_ab _ _
    have e1 : (g ^ k) ^ (Nat.gcdB (Nat.card G) k) = g ^ ((k : ℤ) * Nat.gcdB (Nat.card G) k) := by
      rw [← zpow_natCast g k, ← zpow_mul]
    rw [e1, ← zpow_natCast g (Nat.gcd (Nat.card G) k)]
    conv_rhs => rw [hbz, zpow_add, zpow_mul, hgn, one_zpow, one_mul]
  -- Every subgroup is generated by a natural power of `g` (using q4: it is cyclic).
  have hgen : ∀ H : Subgroup G, ∃ k : ℕ, H = Subgroup.zpowers (g ^ k) := by
    intro H
    letI := q5_subgroup_isCyclic H
    obtain ⟨⟨a, haH⟩, hagen⟩ := IsCyclic.exists_generator (α := H)
    have hHa : H = Subgroup.zpowers a := by
      apply le_antisymm
      · intro x hx
        obtain ⟨m, hm⟩ := hagen ⟨x, hx⟩
        exact ⟨m, by have := Subtype.ext_iff.mp hm; simpa using this⟩
      · rw [Subgroup.zpowers_le]; exact haH
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hg a)
    exact ⟨k, by rw [hHa, ← hk]⟩
  -- Hence a subgroup is pinned down by its order: `H = zpowers (g^{N/|H|})`.
  have hchar : ∀ H : Subgroup G, H = Subgroup.zpowers (g ^ (Nat.card G / Nat.card H)) := by
    intro H
    obtain ⟨k, hk⟩ := hgen H
    have hcard : Nat.card H = Nat.card G / Nat.gcd (Nat.card G) k := by
      rw [hk, Nat.card_zpowers, q2_orderOf_pow g k, hgord]
    have hgcddvd : Nat.gcd (Nat.card G) k ∣ Nat.card G := Nat.gcd_dvd_left _ _
    have hNdivH : Nat.card G / Nat.card H = Nat.gcd (Nat.card G) k := by
      rw [hcard, Nat.div_div_self hgcddvd hNpos.ne']
    rw [hNdivH, hk]
    apply le_antisymm
    · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
      exact ⟨(k / Nat.gcd (Nat.card G) k : ℕ),
        by rw [zpow_natCast, ← pow_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]⟩
    · rw [Subgroup.zpowers_le]; exact hbez k
  -- Existence (`zpowers (g^{N/d})` has order `d`) and uniqueness (via the description above).
  refine ⟨Subgroup.zpowers (g ^ (Nat.card G / d)), ?_, ?_⟩
  · show Nat.card (Subgroup.zpowers (g ^ (Nat.card G / d))) = d
    rw [Nat.card_zpowers, q2_orderOf_pow g (Nat.card G / d), hgord]
    have hdvd2 : Nat.card G / d ∣ Nat.card G := ⟨d, (Nat.div_mul_cancel hd).symm⟩
    rw [Nat.gcd_eq_right hdvd2, Nat.div_div_self hd hNpos.ne']
  · intro H hH
    rw [hchar H, hH]


theorem q7_cyclic_iff_full_order [Fintype G] :
    IsCyclic G ↔ ∃ g : G, orderOf g = Fintype.card G := by
  -- Cyclic means a single element runs through the whole group — i.e. an element whose order
  -- equals the group's size.
  constructor
  · intro _
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]⟩
  · rintro ⟨g, hg⟩
    exact isCyclic_of_orderOf_eq_card g (by rw [hg, Nat.card_eq_fintype_card])


theorem q8_card_generators_zmod :
    (Finset.univ.filter (fun a : ZMod 12 => Nat.Coprime a.val 12)).card = Nat.totient 12 := by
  -- The generators of `ℤ/12` are the residues coprime to `12` (q4 listed them); counting them gives
  -- Euler's totient `φ(12) = 4`.
  decide


theorem q9_int_generators (a : ℤ) :
    AddSubgroup.zmultiples a = ⊤ ↔ a = 1 ∨ a = -1 := by
  -- `a` generates `(ℤ, +)` iff `1` is an integer multiple of `a`, i.e. `a ∣ 1`, i.e. `a = ±1`.
  rw [← Int.isUnit_iff]
  constructor
  · intro h
    have h1 : (1 : ℤ) ∈ AddSubgroup.zmultiples a := by rw [h]; exact AddSubgroup.mem_top 1
    rw [AddSubgroup.mem_zmultiples_iff] at h1
    obtain ⟨k, hk⟩ := h1
    rw [zsmul_eq_mul, Int.cast_id] at hk
    exact (Units.mkOfMulEqOne a k (by rw [mul_comm]; exact hk)).isUnit
  · intro h
    obtain ⟨b, hb⟩ := IsUnit.exists_right_inv h
    rw [AddSubgroup.eq_top_iff']
    intro x
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨x * b, ?_⟩
    rw [zsmul_eq_mul, Int.cast_id, mul_assoc, mul_comm b a, hb, mul_one]


theorem q10_klein_not_cyclic : ¬ IsAddCyclic (ZMod 2 × ZMod 2) := by
  -- A generator would have order `4`, but every element `x` satisfies `2 • x = 0`, so no element
  -- has order exceeding `2`.
  intro h
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := ZMod 2 × ZMod 2)
  have h2 : ∀ x : ZMod 2 × ZMod 2, (2 : ℕ) • x = 0 := by decide
  have hdvd : addOrderOf g ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (h2 g)
  have hcard : addOrderOf g = Nat.card (ZMod 2 × ZMod 2) :=
    addOrderOf_eq_card_of_forall_mem_zmultiples hg
  rw [show Nat.card (ZMod 2 × ZMod 2) = 4 from by rw [Nat.card_eq_fintype_card]; decide] at hcard
  rw [hcard] at hdvd
  exact absurd hdvd (by decide)


theorem q11_roots_of_unity (n : ℕ) [NeZero n] :
    IsCyclic (rootsOfUnity n ℂ) ∧ Nat.card (rootsOfUnity n ℂ) = n :=
  -- The `n`-th roots of unity form a finite subgroup of the units of a field, hence are cyclic;
  -- and over `ℂ` there are exactly `n` of them (the field is algebraically closed).
  ⟨rootsOfUnity.isCyclic ℂ n, Complex.card_rootsOfUnity n⟩

end Solutions.GroupTheory.Cyclic
