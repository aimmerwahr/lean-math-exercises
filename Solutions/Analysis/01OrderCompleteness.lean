import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Solutions.Analysis.OrderCompleteness

open Filter Set

theorem q1_integer_fractional_decomposition (x : ℝ) :
    ∃! p : ℤ × ℝ, x = (p.1 : ℝ) + p.2 ∧ 0 ≤ p.2 ∧ p.2 < 1 := by
  -- The integer part fixes the only possible unit interval containing `x`.
  refine ⟨(⌊x⌋, Int.fract x), ?_, ?_⟩
  · constructor
    · dsimp
      rw [← Int.self_sub_floor]
      ring
    · constructor
      · rw [← Int.self_sub_floor]
        exact sub_nonneg.mpr (Int.floor_le x)
      · rw [← Int.self_sub_floor, sub_lt_iff_lt_add]
        nlinarith [Int.lt_floor_add_one x]
  · rintro ⟨z, u⟩ ⟨hxu, hu0, hu1⟩
    change x = (z : ℝ) + u at hxu
    have hz : (z : ℝ) ≤ x := by linarith
    have hxz : x < (z : ℝ) + 1 := by linarith
    have hfloor : ⌊x⌋ = z := Int.floor_eq_iff.mpr ⟨hz, hxz⟩
    subst z
    apply Prod.ext
    · simp
    · dsimp
      rw [← Int.self_sub_floor]
      linarith


theorem q2_naturals_unbounded (x : ℝ) : ∃ n : ℕ, x < n := by
  -- A hypothetical upper bound has a least one, but its successor still lies in the same set.
  by_contra h
  push Not at h
  let S : Set ℝ := Set.range fun n : ℕ => (n : ℝ)
  have hS : S.Nonempty := ⟨0, ⟨0, by norm_num⟩⟩
  have hSb : BddAbove S := ⟨x, by rintro _ ⟨n, rfl⟩; exact h n⟩
  obtain ⟨n, hnS, hn⟩ := (lt_csSup_iff hSb hS).mp (sub_lt_self (sSup S) zero_lt_one)
  rcases hnS with ⟨n, rfl⟩
  have hsucc : sSup S < (n + 1 : ℕ) := by
    norm_num at hn ⊢
    linarith
  have hsucc_mem : ((n + 1 : ℕ) : ℝ) ≤ sSup S :=
    le_csSup hSb ⟨n + 1, rfl⟩
  linarith


theorem q3_archimedean_reciprocal {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ) < ε := by
  -- Choose an integer beyond the reciprocal scale and invert the resulting inequality.
  obtain ⟨n, hn⟩ := q2_naturals_unbounded (1 / ε)
  have hn_pos : 0 < (n : ℝ) := by
    have : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  refine ⟨n, by exact_mod_cast hn_pos, ?_⟩
  apply (div_lt_iff₀ hn_pos).mpr
  have hmul := (div_lt_iff₀ hε).mp hn
  nlinarith


theorem q4_rational_between {x y : ℝ} (hxy : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := by
  -- After magnifying the interval past unit length, its first integer point gives a rational.
  have hδ : 0 < y - x := sub_pos.mpr hxy
  obtain ⟨n, hn⟩ := q2_naturals_unbounded (1 / (y - x))
  have hn_pos : 0 < (n : ℝ) := by
    have : 0 < 1 / (y - x) := one_div_pos.mpr hδ
    linarith
  have hnd : 1 < (n : ℝ) * (y - x) := by
    exact (div_lt_iff₀ hδ).mp hn
  let k : ℤ := ⌊(n : ℝ) * x⌋ + 1
  have hkx : (n : ℝ) * x < (k : ℝ) := by
    dsimp [k]
    rw [Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one ((n : ℝ) * x)
  have hkx' : (k : ℝ) ≤ (n : ℝ) * x + 1 := by
    have hfloor := Int.floor_le ((n : ℝ) * x)
    dsimp [k]
    push_cast
    linarith
  have hky : (k : ℝ) < (n : ℝ) * y := by
    nlinarith
  refine ⟨(k : ℚ) / n, ?_, ?_⟩
  · simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact (lt_div_iff₀ hn_pos).mpr (by nlinarith)
  · simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact (div_lt_iff₀ hn_pos).mpr (by nlinarith)


theorem q5_rational_approximation (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, |x - (q : ℝ)| < ε := by
  -- A rational in the symmetric epsilon interval has exactly the required error bound.
  obtain ⟨q, hq₁, hq₂⟩ := q4_rational_between (x := x - ε) (y := x + ε) (by linarith)
  refine ⟨q, (abs_lt).mpr ?_⟩
  constructor <;> linarith


theorem q6_sup_approximation {A : Set ℝ} (hA : A.Nonempty) (_hAb : BddAbove A) {ε : ℝ}
    (hε : 0 < ε) : ∃ a ∈ A, sSup A - ε < a := by
  -- Any number strictly below the least upper bound fails to be an upper bound.
  by_contra h
  push Not at h
  have hle : sSup A ≤ sSup A - ε := csSup_le hA h
  linarith


theorem q7_sup_translate {A : Set ℝ} (hA : A.Nonempty) (hAb : BddAbove A) (t : ℝ) :
    sSup {x | ∃ a ∈ A, x = t + a} = t + sSup A := by
  -- Translation preserves the order of all upper bounds.
  let C : Set ℝ := {x | ∃ a ∈ A, x = t + a}
  have hC : C.Nonempty := by
    rcases hA with ⟨a₀, ha₀⟩
    exact ⟨t + a₀, a₀, ha₀, rfl⟩
  have hCb : BddAbove C := by
    rcases hAb with ⟨M, hM⟩
    refine ⟨t + M, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    linarith [hM ha]
  change sSup C = t + sSup A
  apply le_antisymm
  · apply csSup_le hC
    rintro _ ⟨a, ha, rfl⟩
    linarith [le_csSup hAb ha]
  · have hA_upper : sSup A ≤ sSup C - t := by
      apply csSup_le hA
      intro a ha
      have hmem : t + a ∈ C := ⟨a, ha, rfl⟩
      have hle := le_csSup hCb hmem
      linarith
    linarith


theorem q8_sup_sumset {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) (hAb : BddAbove A)
    (hBb : BddAbove B) :
    sSup {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b} = sSup A + sSup B := by
  -- Upper bounds add, and two independently chosen near-maximizers nearly attain their sum.
  let C : Set ℝ := {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}
  have hC : C.Nonempty := by
    rcases hA with ⟨a₀, ha₀⟩
    rcases hB with ⟨b₀, hb₀⟩
    exact ⟨a₀ + b₀, a₀, ha₀, b₀, hb₀, rfl⟩
  have hCb : BddAbove C := by
    rcases hAb with ⟨M, hM⟩
    rcases hBb with ⟨N, hN⟩
    refine ⟨M + N, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    linarith [hM ha, hN hb]
  change sSup C = sSup A + sSup B
  apply le_antisymm
  · apply csSup_le hC
    rintro _ ⟨a, ha, b, hb, rfl⟩
    linarith [le_csSup hAb ha, le_csSup hBb hb]
  · by_contra h
    have hlt : sSup C < sSup A + sSup B := lt_of_not_ge h
    let ε : ℝ := (sSup A + sSup B - sSup C) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨a, ha, hsa⟩ := q6_sup_approximation hA hAb hε
    obtain ⟨b, hb, hsb⟩ := q6_sup_approximation hB hBb hε
    have hmem : a + b ∈ C := ⟨a, ha, b, hb, rfl⟩
    have hle := le_csSup hCb hmem
    dsimp [ε] at hsa hsb
    linarith


def sqrtTwoSet : Set ℝ := {x | 0 ≤ x ∧ x ^ 2 < 2}

theorem q9_sqrtTwoSet_nonempty_bddAbove : sqrtTwoSet.Nonempty ∧ BddAbove sqrtTwoSet := by
  -- Zero lies in the set, while the elementary inequality `x² < 2` keeps every member below two.
  have h0 : (0 : ℝ) ∈ sqrtTwoSet := by
    simp [sqrtTwoSet]
  refine ⟨⟨0, h0⟩, ?_⟩
  refine ⟨2, ?_⟩
  intro x hx
  rcases hx with ⟨hx0, hx2⟩
  nlinarith


theorem q10_sSup_sqrtTwoSet_sq_not_lt : ¬ sSup sqrtTwoSet ^ 2 < 2 := by
  -- If the square were too small, a positive displacement would remain in the set while passing
  -- its supremum.
  obtain ⟨_, hbdd⟩ := q9_sqrtTwoSet_nonempty_bddAbove
  intro hlt
  let s : ℝ := sSup sqrtTwoSet
  change s ^ 2 < 2 at hlt
  have hs0 : 0 ≤ s := by
    simpa [s] using le_csSup hbdd (by simp [sqrtTwoSet])
  let d : ℝ := (2 - s ^ 2) / (4 * (s + 1))
  have hden : 0 < 4 * (s + 1) := by nlinarith
  have hd0 : 0 < d := by
    dsimp [d]
    exact div_pos (by linarith) hden
  have hdeq : 4 * (s + 1) * d = 2 - s ^ 2 := by
    dsimp [d]
    field_simp
  have hd1 : d ≤ 1 := by
    dsimp [d]
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg s]
  have hdsq : d ^ 2 ≤ d := by
    nlinarith [mul_nonneg (le_of_lt hd0) (sub_nonneg.mpr hd1)]
  have hnew_sq : (s + d) ^ 2 < 2 := by
    nlinarith
  have hnew : s + d ∈ sqrtTwoSet := by
    exact ⟨by linarith, hnew_sq⟩
  have hle : s + d ≤ s := by
    simpa [s] using le_csSup hbdd hnew
  linarith


theorem q11_sSup_sqrtTwoSet_sq_not_gt : ¬ 2 < sSup sqrtTwoSet ^ 2 := by
  -- If the square were too large, a positive displacement downward would still be an upper bound,
  -- contradicting leastness of the supremum.
  obtain ⟨hne, hbdd⟩ := q9_sqrtTwoSet_nonempty_bddAbove
  intro hgt
  let s : ℝ := sSup sqrtTwoSet
  change 2 < s ^ 2 at hgt
  have hs0 : 0 ≤ s := by
    simpa [s] using le_csSup hbdd (by simp [sqrtTwoSet])
  let d : ℝ := (s ^ 2 - 2) / (4 * (s + 1))
  have hden : 0 < 4 * (s + 1) := by nlinarith
  have hd0 : 0 < d := by
    dsimp [d]
    exact div_pos (by linarith) hden
  have hdeq : 4 * (s + 1) * d = s ^ 2 - 2 := by
    dsimp [d]
    field_simp
  have hsd0 : 0 ≤ s - d := by
    apply sub_nonneg.mpr
    dsimp [d]
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg s]
  have hsd_sq : 2 < (s - d) ^ 2 := by
    nlinarith [sq_nonneg d]
  have hup : ∀ x ∈ sqrtTwoSet, x ≤ s - d := by
    intro x hx
    rcases hx with ⟨hx0, hx2⟩
    by_contra hxs
    have hsx : s - d < x := lt_of_not_ge hxs
    have hsq : (s - d) ^ 2 < x ^ 2 := (sq_lt_sq₀ hsd0 hx0).mpr hsx
    linarith
  have hle : s ≤ s - d := by
    simpa [s] using csSup_le hne hup
  linarith


theorem q12_square_root_two_from_supremum : sSup sqrtTwoSet ^ 2 = 2 := by
  -- The two preceding exclusions leave equality as the only possible comparison.
  rcases lt_trichotomy (sSup sqrtTwoSet ^ 2) 2 with hlt | heq | hgt
  · exact (q10_sSup_sqrtTwoSet_sq_not_lt hlt).elim
  · exact heq
  · exact (q11_sSup_sqrtTwoSet_sq_not_gt hgt).elim


theorem q13_nested_intervals_nonempty {a b : ℕ → ℝ} (ha : Monotone a) (hb : Antitone b)
    (hab : ∀ n, a n ≤ b n) :
    ∃ x : ℝ, x ∈ ⋂ n, Set.Icc (a n) (b n) := by
  -- The supremum of the left endpoints lies above every left endpoint and below every right
  -- endpoint, so it lies in all the intervals.
  let S : Set ℝ := Set.range a
  have hS : S.Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
  have hSb : BddAbove S := by
    refine ⟨b 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hab n).trans (hb (Nat.zero_le n))
  let s : ℝ := sSup S
  have hleft : ∀ n, a n ≤ s := fun n ↦ le_csSup hSb ⟨n, rfl⟩
  have hright : ∀ n, s ≤ b n := by
    intro n
    apply csSup_le hS
    rintro _ ⟨m, rfl⟩
    rcases le_total m n with hmn | hnm
    · exact (ha hmn).trans (hab n)
    · exact (hab m).trans (hb hnm)
  refine ⟨s, ?_⟩
  rw [mem_iInter]
  intro n
  exact ⟨hleft n, hright n⟩


theorem q14_nested_intervals_unique {a b : ℕ → ℝ}
    (hshrink : Tendsto (fun n => b n - a n) atTop (nhds 0)) {x y : ℝ}
    (hx : x ∈ ⋂ n, Set.Icc (a n) (b n)) (hy : y ∈ ⋂ n, Set.Icc (a n) (b n)) : x = y := by
  -- Two common points would be separated by a positive distance, although every interval
  -- containing both eventually has smaller length than that distance.
  apply le_antisymm
  · by_contra hxy
    have hyx : y < x := lt_of_not_ge hxy
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hshrink) (x - y) (by linarith)
    have hxN := mem_iInter.mp hx N
    have hyN := mem_iInter.mp hy N
    have hgap0 : 0 ≤ b N - a N := by linarith [hxN.1, hxN.2]
    have hgap : b N - a N < x - y := by
      simpa [Real.dist_eq, abs_of_nonneg hgap0] using hN N le_rfl
    linarith [hxN.1, hxN.2, hyN.1, hyN.2]
  · by_contra hyx
    have hxy : x < y := lt_of_not_ge hyx
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hshrink) (y - x) (by linarith)
    have hxN := mem_iInter.mp hx N
    have hyN := mem_iInter.mp hy N
    have hgap0 : 0 ≤ b N - a N := by linarith [hxN.1, hxN.2]
    have hgap : b N - a N < y - x := by
      simpa [Real.dist_eq, abs_of_nonneg hgap0] using hN N le_rfl
    linarith [hxN.1, hxN.2, hyN.1, hyN.2]

end Solutions.Analysis.OrderCompleteness
