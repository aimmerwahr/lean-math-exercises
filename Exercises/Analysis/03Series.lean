import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Exercises — Analysis / Series

A series is understood through its partial sums. Absolute convergence makes comparison possible,
while conditional convergence shows that cancellation can be decisive. Geometric estimates turn
eventual decay into convergence and underlie the ratio and root tests.

Prove each statement yourself; the canonical proofs live in `Solutions/Analysis/03Series.lean`.
Do **not** commit your proofs into this file.
-/

namespace Exercises.Analysis.Series

open Filter BigOperators

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section
-- extending and comparing finite partial sums
#check @Finset.sum_range_succ
#check @Finset.sum_Icc_succ_top
#check @Finset.sum_le_sum
-- translating between a series and its partial sums
#check @HasSum.tendsto_sum_nat
#check @hasSum_iff_tendsto_nat_of_nonneg
#check @summable_nat_add_iff
-- grouping a positive decreasing series into dyadic blocks
#check @summable_condensed_iff_of_nonneg
-- passing from absolute convergence to convergence
#check @Metric.tendsto_atTop
end

/-- **Question 1.**

For `r ≠ 1`, prove `∑_{k=0}^n r^k = (1-r^(n+1))/(1-r)`.

Prove without using `geom_sum_eq`, `geom_sum_mul_neg`, or a finite geometric-sum closed form. -/
theorem q1_geometric_partial_sum {r : ℝ} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), r ^ k = (1 - r ^ (n + 1)) / (1 - r) := by sorry


/-- **Question 2.**

For every natural number `n`, prove `∑_{k=1}^n 1/(k(k+1)) = n/(n+1)`. -/
theorem q2_reciprocal_telescoping_sum (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k * (k + 1)) = n / (n + 1) := by sorry


/-- **Question 3.**

For nonnegative terms, `∑ a_n` converges exactly when its partial sums are bounded above.

Prove without using `summable_of_sum_range_le` or
`summable_iff_not_tendsto_nat_atTop_of_nonneg`. -/
theorem q3_nonnegative_summable_iff_bounded_partial_sums {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) :
    Summable a ↔ BddAbove (Set.range fun N => ∑ n ∈ Finset.range N, a n) := by sorry


/-- **Question 4.**

If `0 ≤ a_n ≤ b_n` and `∑ b_n` converges, then `∑ a_n` converges and `∑' a_n ≤ ∑' b_n`.

Prove without using `Summable.of_nonneg_of_le` or `Summable.tsum_le_tsum`. -/
theorem q4_comparison_test_nonnegative {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hab : ∀ n, a n ≤ b n) (hb : Summable b) : Summable a ∧ ∑' n, a n ≤ ∑' n, b n := by sorry


/-- **Question 5.**

If `|r| < 1`, then every partial sum of `∑ |r|^n` is at most `1/(1-|r|)`.

Prove without using `geom_sum_eq`. -/
theorem q5_geometric_absolute_partial_sum_le {r : ℝ} (hr : |r| < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, |r| ^ n ≤ 1 / (1 - |r|) := by sorry


/-- **Question 6.**

If `|r| < 1`, then `∑ |r|^n` converges.

Use Question 5 to bound the partial sums.

Prove without using `summable_geometric_of_lt_one` or `summable_geometric_of_abs_lt_one`. -/
theorem q6_geometric_absolute_summable {r : ℝ} (hr : |r| < 1) :
    Summable (fun n : ℕ => |r| ^ n) := by sorry


/-- **Question 7.**

If `|r| < 1`, the partial sums of `∑ r^n` converge to `1/(1-r)`. -/

theorem q7_geometric_partial_sums_tendsto {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, r ^ n) atTop (nhds (1 / (1 - r))) := by sorry


/-- **Question 8.**

If `|r| < 1`, then `∑' r^n = 1/(1-r)`.

Use Questions 6 and 7 to translate the partial-sum limit into a series evaluation.

Prove without using `hasSum_geometric_of_norm_lt_one`, `tsum_geometric_of_norm_lt_one`,
`hasSum_geometric_of_abs_lt_one`, or `tsum_geometric_of_abs_lt_one`. -/
theorem q8_geometric_has_sum {r : ℝ} (hr : |r| < 1) : ∑' n : ℕ, r ^ n = 1 / (1 - r) := by sorry


/-- **Question 9.**

Evaluate `∑'_{n=0}^∞ (-1/2)^n` without an exact geometric-series evaluation lemma.

Use Question 8.

Prove without using `hasSum_geometric_of_norm_lt_one`, `tsum_geometric_of_norm_lt_one`,
`hasSum_geometric_of_abs_lt_one`, or `tsum_geometric_of_abs_lt_one`. -/
theorem q9_alternating_geometric_sum : ∑' n : ℕ, (-1 / 2 : ℝ) ^ n = 2 / 3 := by sorry


/-- **Question 10.**

For `p ∈ ℝ` and `k ∈ ℕ`, simplify the `k`th term of the condensed `p`-series:
`2^k / (2^k)^p = (2^(1-p))^k`. -/

theorem q10_condensed_p_series_term (p : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ) ^ p)⁻¹ = (2 ^ (1 - p)) ^ k := by sorry


/-- **Question 11.**

If `p < 0`, then the terms `1/n^p` do not form a summable series. -/

theorem q11_negative_p_series_not_summable {p : ℝ} (hp : p < 0) :
    ¬Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) := by sorry


/-- **Question 12.**

The `p`-series `∑_{n=1}^∞ 1/n^p` converges exactly when `1 < p`.

Use Questions 10 and 11.

Prove without using `Real.summable_one_div_nat_rpow` or `Real.summable_nat_rpow_inv`. -/
theorem q12_p_series_threshold (p : ℝ) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) ↔ 1 < p := by sorry


/-- **Question 13.**

An eventual ratio bound `|a_{n+1}| ≤ r|a_n|` with `0 ≤ r < 1` implies absolute convergence.

Prove without using `summable_of_ratio_norm_eventually_le`. -/
theorem q13_ratio_test_eventual {a : ℕ → ℝ} {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (h_ratio : ∀ n ≥ N, |a (n + 1)| ≤ r * |a n|) : Summable (fun n => |a n|) := by sorry


/-- **Question 14.**

For every real `x`, the series `∑ |x|^n/n!` converges.

Prove without using `Real.summable_pow_div_factorial`. -/
theorem q14_exp_series_summable (x : ℝ) : Summable (fun n : ℕ => |x| ^ n / n.factorial) := by sorry


/-- **Question 15.**

An eventual bound `|a_n|^(1/n) ≤ r < 1` implies absolute convergence. -/
theorem q15_root_test_eventual {a : ℕ → ℝ} {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hroot : ∀ n ≥ N, 0 < n → |a n| ^ ((n : ℝ)⁻¹) ≤ r) : Summable (fun n => |a n|) := by sorry

end Exercises.Analysis.Series
