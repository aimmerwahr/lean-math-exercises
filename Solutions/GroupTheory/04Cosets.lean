import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Solutions.GroupTheory.Cosets

open Pointwise

variable {G : Type*} [Group G]

theorem q1_coset_card (g : G) (H : Subgroup G) :
    (g • (H : Set G)).ncard = (H : Set G).ncard := by
  -- Left multiplication by `g` is a bijection `G → G`, so it carries `H` onto the coset `gH`
  -- without changing its size.
  exact Set.ncard_smul_set g (H : Set G)


theorem q2_lagrange [Finite G] (H : Subgroup G) : Nat.card H ∣ Nat.card G := by
  -- The cosets of `H` partition `G` into `[G : H]` blocks each the size of `H`, so
  -- `|G| = [G : H] · |H|` and `|H|` divides `|G|`.
  exact ⟨Nat.card (G ⧸ H), by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H, Nat.mul_comm]⟩


theorem q3_orderOf_dvd_card [Finite G] (g : G) : orderOf g ∣ Nat.card G := by
  -- The order of `g` is the size of the cyclic subgroup `⟨g⟩`, which divides `|G|` by Lagrange.
  rw [← Nat.card_zpowers g]
  exact q2_lagrange (Subgroup.zpowers g)


theorem q4_prime_order_cyclic [Finite G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p) : IsCyclic G := by
  -- Take any `g ≠ 1`. Its order divides `p`, and is not `1`, so it is `p = |G|`; hence `g`
  -- generates the whole group.
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hdvd : orderOf g ∣ p := hcard ▸ q3_orderOf_dvd_card g
  rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h1 | hpe
  · exact absurd (orderOf_eq_one_iff.mp h1) hg
  · exact isCyclic_of_orderOf_eq_card g (by rw [hpe, hcard])


theorem q5_fermat_little {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  -- In the field `ZMod p`, `a ≠ 0` is a unit; the unit group has `p - 1` elements, so the order of
  -- `a` divides `p - 1` and `a^{p-1} = 1`.
  obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr ha
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  have h1 : orderOf u ∣ (p - 1) := hcard ▸ q3_orderOf_dvd_card u
  have h2 : u ^ (p - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]


theorem q6_euler {n : ℕ} [NeZero n] (a : ZMod n) (ha : IsUnit a) :
    a ^ n.totient = 1 := by
  -- The units of `ZMod n` form a group of order `φ(n)`, so the order of the unit `a` divides
  -- `φ(n)` and `a^{φ(n)} = 1`.
  obtain ⟨u, rfl⟩ := ha
  have hcard : Nat.card (ZMod n)ˣ = n.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h1 : orderOf u ∣ n.totient := hcard ▸ q3_orderOf_dvd_card u
  have h2 : u ^ n.totient = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]


theorem q7_cosets_count :
    Nat.card (Equiv.Perm (Fin 3)) = 6 ∧ Nat.card (alternatingGroup (Fin 3)) = 3 := by
  -- `S₃` has `3! = 6` elements and its alternating subgroup `A₃` has `3`; Lagrange is the visible
  -- `6 = 3 · 2` (two cosets of `A₃`).
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine ⟨?_, ?_⟩ <;> decide


theorem q8_no_proper_subgroups [Finite G] [Nontrivial G]
    (h : ∀ K : Subgroup G, K = ⊥ ∨ K = ⊤) : (Nat.card G).Prime := by
  -- A nonidentity `g` generates a nontrivial subgroup, which must be all of `G`, so `G` is cyclic.
  -- Were `|G|` composite, its smallest prime factor would give a proper nontrivial subgroup — barred
  -- by hypothesis. So `|G|` is prime.
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have htop : Subgroup.zpowers g = ⊤ := by
    rcases h (Subgroup.zpowers g) with hb | ht
    · exact absurd (Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_zpowers g)) hg
    · exact ht
  have hgord : orderOf g = Nat.card G := by
    rw [← Nat.card_zpowers g, htop]; exact Nat.card_congr (Subgroup.topEquiv.toEquiv)
  -- `|G| ≥ 2`
  have h2 : 2 ≤ Nat.card G := by
    rw [← hgord]
    have hne : orderOf g ≠ 1 := fun hh => hg (orderOf_eq_one_iff.mp hh)
    have hpos := orderOf_pos g
    omega
  by_contra hnp
  -- smallest prime factor `q` of `|G|` gives a proper nontrivial subgroup
  set n := Nat.card G with hn
  have hqp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hqdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hn0 : 0 < n := by omega
  have hqlt : n.minFac < n := by
    rcases (Nat.minFac_le hn0).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ hqp) hnp
  -- the subgroup `⟨g^{n/q}⟩` has order `q`, so it is neither `⊥` nor `⊤`
  have hd : n / n.minFac ∣ n := ⟨n.minFac, (Nat.div_mul_cancel hqdvd).symm⟩
  have horder : orderOf (g ^ (n / n.minFac)) = n.minFac := by
    rw [orderOf_pow, hgord, Nat.gcd_eq_right hd, Nat.div_div_self hqdvd (by omega)]
  set K := Subgroup.zpowers (g ^ (n / n.minFac)) with hK
  have hKcard : Nat.card K = n.minFac := by rw [hK, Nat.card_zpowers, horder]
  rcases h K with hb | ht
  · have h1 : g ^ (n / n.minFac) = 1 := by
      have hmem : g ^ (n / n.minFac) ∈ K := Subgroup.mem_zpowers _
      rw [hb, Subgroup.mem_bot] at hmem; exact hmem
    rw [h1, orderOf_one] at horder
    have := hqp.two_le; omega
  · have hcardtop : Nat.card K = n := by rw [ht]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hKcard] at hcardtop; omega

end Solutions.GroupTheory.Cosets
