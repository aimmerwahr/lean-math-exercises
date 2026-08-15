import Exercises.Analysis.«03Series»
import Solutions.Analysis.«03Series»
import Mathlib.Analysis.PSeries
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Analysis.Series.q1_geometric_partial_sum
  [geom_sum_eq, geom_sum_mul_neg, geom_sum_mul]
assert_not_uses Solutions.Analysis.Series.q1_geometric_partial_sum
  [geom_sum_eq, geom_sum_mul_neg, geom_sum_mul]

assert_not_uses Exercises.Analysis.Series.q3_nonnegative_summable_iff_bounded_partial_sums
  [summable_of_sum_range_le, summable_iff_not_tendsto_nat_atTop_of_nonneg]
assert_not_uses Solutions.Analysis.Series.q3_nonnegative_summable_iff_bounded_partial_sums
  [summable_of_sum_range_le, summable_iff_not_tendsto_nat_atTop_of_nonneg]

assert_not_uses Exercises.Analysis.Series.q4_comparison_test_nonnegative
  [Summable.of_nonneg_of_le, Summable.tsum_le_tsum]
assert_not_uses Solutions.Analysis.Series.q4_comparison_test_nonnegative
  [Summable.of_nonneg_of_le, Summable.tsum_le_tsum]

assert_not_uses Exercises.Analysis.Series.q5_geometric_absolute_partial_sum_le
  [geom_sum_eq]
assert_not_uses Solutions.Analysis.Series.q5_geometric_absolute_partial_sum_le
  [geom_sum_eq]

assert_not_uses Exercises.Analysis.Series.q6_geometric_absolute_summable
  [summable_geometric_of_lt_one, summable_geometric_of_abs_lt_one]
assert_not_uses Solutions.Analysis.Series.q6_geometric_absolute_summable
  [summable_geometric_of_lt_one, summable_geometric_of_abs_lt_one]

assert_not_uses Exercises.Analysis.Series.q8_geometric_has_sum
  [hasSum_geometric_of_norm_lt_one, tsum_geometric_of_norm_lt_one,
    hasSum_geometric_of_abs_lt_one, tsum_geometric_of_abs_lt_one]
assert_not_uses Solutions.Analysis.Series.q8_geometric_has_sum
  [hasSum_geometric_of_norm_lt_one, tsum_geometric_of_norm_lt_one,
    hasSum_geometric_of_abs_lt_one, tsum_geometric_of_abs_lt_one]

assert_not_uses Exercises.Analysis.Series.q9_alternating_geometric_sum
  [hasSum_geometric_of_norm_lt_one, tsum_geometric_of_norm_lt_one,
    hasSum_geometric_of_abs_lt_one, tsum_geometric_of_abs_lt_one]
assert_not_uses Solutions.Analysis.Series.q9_alternating_geometric_sum
  [hasSum_geometric_of_norm_lt_one, tsum_geometric_of_norm_lt_one,
    hasSum_geometric_of_abs_lt_one, tsum_geometric_of_abs_lt_one]

assert_not_uses Exercises.Analysis.Series.q12_p_series_threshold
  [Real.summable_one_div_nat_rpow, Real.summable_nat_rpow_inv]
assert_not_uses Solutions.Analysis.Series.q12_p_series_threshold
  [Real.summable_one_div_nat_rpow, Real.summable_nat_rpow_inv]

assert_not_uses Exercises.Analysis.Series.q13_ratio_test_eventual
  [summable_of_ratio_norm_eventually_le, summable_of_ratio_test_tendsto_lt_one]
assert_not_uses Solutions.Analysis.Series.q13_ratio_test_eventual
  [summable_of_ratio_norm_eventually_le, summable_of_ratio_test_tendsto_lt_one]

assert_not_uses Exercises.Analysis.Series.q14_exp_series_summable [Real.summable_pow_div_factorial]
assert_not_uses Solutions.Analysis.Series.q14_exp_series_summable [Real.summable_pow_div_factorial]
