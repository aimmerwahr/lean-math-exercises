import Exercises.Analysis.«03Series»
import Solutions.Analysis.«02RealSequences»
import Mathlib.Tactic

namespace Solutions.Analysis.Series

open Filter BigOperators Finset

theorem q1_geometric_partial_sum {r : ℝ} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), r ^ k = (1 - r ^ (n + 1)) / (1 - r) := by
  induction n with
  | zero =>
    simp
    field_simp [hr]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp [hr]
    ring


theorem q2_reciprocal_telescoping_sum (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k * (k + 1)) = n / (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp
    ring


theorem q3_nonnegative_summable_iff_bounded_partial_sums {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) :
    Summable a ↔ BddAbove (Set.range fun N => ∑ n ∈ Finset.range N, a n) := by
  constructor
  · intro hsum
    refine ⟨∑' n, a n, ?_⟩
    rintro x ⟨N, rfl⟩
    exact hsum.sum_le_tsum (Finset.range N) fun n _ => ha n
  · intro hbounded
    have hmono : Monotone (fun N => ∑ n ∈ Finset.range N, a n) := by
      intro m n hmn
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) ?_
      intro i _ _
      exact ha i
    -- The partial sums increase to their least upper bound.
    have hlimit := Solutions.Analysis.RealSequences.q4_monotone_tends_to_sup hmono hbounded
    exact ⟨sSup (Set.range fun N => ∑ n ∈ Finset.range N, a n),
      (hasSum_iff_tendsto_nat_of_nonneg ha _).mpr hlimit⟩


theorem q4_comparison_test_nonnegative {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hab : ∀ n, a n ≤ b n) (hb : Summable b) : Summable a ∧ ∑' n, a n ≤ ∑' n, b n := by
  have hbounded : BddAbove (Set.range fun N => ∑ n ∈ Finset.range N, a n) := by
    refine ⟨∑' n, b n, ?_⟩
    rintro x ⟨N, rfl⟩
    calc
      ∑ n ∈ Finset.range N, a n ≤ ∑ n ∈ Finset.range N, b n :=
        Finset.sum_le_sum fun n _ => hab n
      _ ≤ ∑' n, b n := hb.sum_le_tsum _ fun n _ => le_trans (ha n) (hab n)
  have hsum_a := (q3_nonnegative_summable_iff_bounded_partial_sums ha).mpr hbounded
  constructor
  · exact hsum_a
  · -- Every partial sum of `a` is bounded by the total sum of its majorant.
    apply le_of_tendsto' hsum_a.hasSum.tendsto_sum_nat
    intro N
    calc
      ∑ n ∈ Finset.range N, a n ≤ ∑ n ∈ Finset.range N, b n :=
        Finset.sum_le_sum fun n _ => hab n
      _ ≤ ∑' n, b n := hb.sum_le_tsum _ fun n _ => le_trans (ha n) (hab n)


theorem q5_geometric_absolute_partial_sum_le {r : ℝ} (hr : |r| < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, |r| ^ n ≤ 1 / (1 - |r|) := by
  have hden : 0 < 1 - |r| := by linarith
  have hne : |r| ≠ 1 := by linarith
  cases N with
  | zero => positivity
  | succ N =>
    -- The finite formula leaves a nonnegative remainder after multiplication by `1 - |r|`.
    change ∑ n ∈ Finset.range (N + 1), |r| ^ n ≤ 1 / (1 - |r|)
    rw [q1_geometric_partial_sum hne N]
    apply (div_le_iff₀ hden).mpr
    have hpow : 0 ≤ |r| ^ (N + 1) := pow_nonneg (abs_nonneg r) _
    have hcancel : 1 / (1 - |r|) * (1 - |r|) = 1 := by
      field_simp
    rw [hcancel]
    linarith


theorem q6_geometric_absolute_summable {r : ℝ} (hr : |r| < 1) :
    Summable (fun n : ℕ => |r| ^ n) := by
  -- Question 5 supplies one common upper bound for all nonnegative partial sums.
  apply (q3_nonnegative_summable_iff_bounded_partial_sums fun n => pow_nonneg (abs_nonneg r) n).mpr
  refine ⟨1 / (1 - |r|), ?_⟩
  rintro x ⟨N, rfl⟩
  exact q5_geometric_absolute_partial_sum_le hr N


theorem q7_geometric_partial_sums_tendsto {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, r ^ n) atTop (nhds (1 / (1 - r))) := by
  -- The remainder in the finite geometric formula tends to zero.
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1
      (Solutions.Analysis.RealSequences.q3_geometric_tends_to_zero (abs_nonneg r) hr)) ε hε
    refine ⟨N, fun n hn => ?_⟩
    simpa [Real.dist_eq, abs_pow, abs_of_nonneg (pow_nonneg (abs_nonneg r) n)] using hN n hn
  have hrne : r ≠ 1 := by
    intro hrone
    subst r
    norm_num at hr
  have hformula : Tendsto (fun n : ℕ => (1 - r ^ (n + 1)) / (1 - r)) atTop
      (nhds (1 / (1 - r))) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using ((hone.sub (hpow.comp (tendsto_add_atTop_nat 1))).div_const (1 - r))
  have hpartial_shift : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), r ^ k) atTop
      (nhds (1 / (1 - r))) := by
    simpa only [q1_geometric_partial_sum hrne] using hformula
  exact (tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using hpartial_shift)


theorem q8_geometric_has_sum {r : ℝ} (hr : |r| < 1) : ∑' n : ℕ, r ^ n = 1 / (1 - r) := by
  -- Absolute convergence identifies the limit of the partial sums with the infinite sum.
  have hsum : Summable (fun n : ℕ => r ^ n) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs, abs_pow] using q6_geometric_absolute_summable hr
  exact ((hsum.hasSum_iff_tendsto_nat).mpr (q7_geometric_partial_sums_tendsto hr)).tsum_eq


theorem q9_alternating_geometric_sum : ∑' n : ℕ, (-1 / 2 : ℝ) ^ n = 2 / 3 := by
  convert q8_geometric_has_sum (r := -1 / 2) (by norm_num) using 1
  all_goals norm_num


theorem q10_condensed_p_series_term (p : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ) ^ p)⁻¹ = (2 ^ (1 - p)) ^ k := by
  -- Rewrite both factors as real powers of the same positive base.
  simp_rw [Nat.cast_pow, Nat.cast_two, ← Real.rpow_natCast, ← Real.rpow_mul zero_lt_two.le,
    mul_comm _ p, Real.rpow_mul zero_lt_two.le, Real.rpow_natCast, ← inv_pow, ← mul_pow]
  -- Inverting the second factor subtracts its exponent from the first.
  nth_rw 1 [← Real.rpow_one 2]
  rw [← division_def, ← Real.rpow_sub zero_lt_two]


theorem q11_negative_p_series_not_summable {p : ℝ} (hp : p < 0) :
    ¬Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) := by
  intro hsum
  -- A summable series has terms tending to zero, whereas negative powers eventually exceed one.
  obtain ⟨k : ℕ, hklt : ((k : ℝ) ^ p)⁻¹ < 1, hkzero : k ≠ 0⟩ :=
    ((hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and
        (eventually_cofinite_ne 0)).exists
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hkzero
  have hkone : 1 ≤ (k : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkzero)
  -- A nonzero natural number is at least one, and a negative power of it is at most one.
  have hpower : (k : ℝ) ^ p ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hkone hp.le
  have hinv : 1 ≤ ((k : ℝ) ^ p)⁻¹ :=
    (one_le_inv₀ (Real.rpow_pos_of_pos hkpos _)).mpr hpower
  exact (not_lt_of_ge hinv) hklt


theorem q12_p_series_threshold (p : ℝ) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) ↔ 1 < p := by
  have hshift :
      Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) ↔
        Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) := by
    simpa using (summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℝ) ^ p))
  rw [hshift]
  simp only [one_div]
  change Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) ↔ 1 < p
  rcases le_or_gt 0 p with hp | hp
  · rw [← summable_condensed_iff_of_nonneg]
    -- Question 10 turns the condensed series into a geometric series.
    · have hterms : (fun k : ℕ => (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ) ^ p)⁻¹) =
          fun k => (2 ^ (1 - p)) ^ k := by
        funext k
        exact q10_condensed_p_series_term p k
      rw [hterms, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos zero_lt_two _), Real.rpow_lt_one_iff zero_lt_two.le]
      simp
    · intro n
      positivity
    · intro m n hm hmn
      gcongr
  · have hnot_one_lt : ¬1 < p := fun hp_one => hp.not_ge (zero_le_one.trans hp_one.le)
    simpa only [hnot_one_lt, iff_false] using q11_negative_p_series_not_summable hp


theorem q13_ratio_test_eventual {a : ℕ → ℝ} {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (h_ratio : ∀ n ≥ N, |a (n + 1)| ≤ r * |a n|) : Summable (fun n => |a n|) := by
  -- Repeatedly applying the ratio estimate gives a geometric majorant for the tail.
  have htail_bound : ∀ k : ℕ, |a (N + k)| ≤ |a N| * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        |a (N + (k + 1))| = |a ((N + k) + 1)| := by
          congr 2
        _ ≤ r * |a (N + k)| := h_ratio (N + k) (by omega)
        _ ≤ r * (|a N| * r ^ k) := mul_le_mul_of_nonneg_left ih hr
        _ = |a N| * r ^ (k + 1) := by ring
  have hgeometric : Summable (fun k : ℕ => |a N| * r ^ k) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have htail : Summable (fun k : ℕ => |a (N + k)|) :=
    (q4_comparison_test_nonnegative (fun k => abs_nonneg _) htail_bound hgeometric).1
  exact (summable_nat_add_iff N).mp (by simpa [Nat.add_comm] using htail)


theorem q14_exp_series_summable (x : ℝ) : Summable (fun n : ℕ => |x| ^ n / n.factorial) := by
  let N : ℕ := ⌊|x|⌋₊
  let r : ℝ := |x| / (N + 1)
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hr : 0 ≤ r := div_nonneg (abs_nonneg x) hden.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hden).mpr (Nat.lt_floor_add_one _)
  -- Beyond the integer part of `|x|`, the factorial growth makes each successive ratio less than one.
  have hratio : ∀ n ≥ N,
      |(|x| ^ (n + 1) / (n + 1).factorial)| ≤ r * |(|x| ^ n / n.factorial)| := by
    intro n hn
    calc
      |(|x| ^ (n + 1) / (n + 1).factorial)| = |x| / (n + 1) * |(|x| ^ n / n.factorial)| := by
        have hterm : 0 ≤ |x| ^ n / n.factorial := by positivity
        have hterm_succ : 0 ≤ |x| ^ (n + 1) / (n + 1).factorial := by positivity
        rw [abs_of_nonneg hterm_succ, abs_of_nonneg hterm, pow_succ,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, div_mul_div_comm]
        ring
      _ ≤ r * |(|x| ^ n / n.factorial)| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        dsimp [r]
        apply div_le_div₀ (abs_nonneg x) le_rfl hden
        exact_mod_cast Nat.add_le_add_right hn 1
  have hsum := q13_ratio_test_eventual
    (a := fun n : ℕ => |x| ^ n / n.factorial) (N := N) hr hr1 hratio
  exact hsum.congr fun n => abs_of_nonneg (by positivity)


theorem q15_root_test_eventual {a : ℕ → ℝ} {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hroot : ∀ n ≥ N, 0 < n → |a n| ^ ((n : ℝ)⁻¹) ≤ r) : Summable (fun n => |a n|) := by
  let M : ℕ := max N 1
  -- Raising the root estimate to the `n`th power converts it into a geometric bound.
  have hbound : ∀ n ≥ M, |a n| ≤ r ^ n := by
    intro n hn
    have hnpos : 0 < n := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hn)
    have hroot' := hroot n (le_trans (le_max_left _ _) hn) hnpos
    have hraised := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hroot'
      (Nat.cast_nonneg n)
    rw [Real.rpow_inv_rpow (abs_nonneg _) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)),
      Real.rpow_natCast] at hraised
    exact hraised
  have htail_bound : ∀ k : ℕ, |a (M + k)| ≤ r ^ M * r ^ k := by
    intro k
    calc
      |a (M + k)| ≤ r ^ (M + k) := hbound _ (by omega)
      _ = r ^ M * r ^ k := by rw [pow_add]
  have hgeometric : Summable (fun k : ℕ => r ^ M * r ^ k) :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have htail : Summable (fun k : ℕ => |a (M + k)|) :=
    (q4_comparison_test_nonnegative (fun k => abs_nonneg _) htail_bound hgeometric).1
  exact (summable_nat_add_iff M).mp (by simpa [Nat.add_comm] using htail)

end Solutions.Analysis.Series
