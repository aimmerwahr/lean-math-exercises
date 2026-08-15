import Exercises.Analysis.«01OrderCompleteness»
import Solutions.Analysis.«01OrderCompleteness»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Analysis.OrderCompleteness.q2_naturals_unbounded [exists_nat_gt]
assert_not_uses Exercises.Analysis.OrderCompleteness.q3_archimedean_reciprocal
  [tendsto_one_div_atTop_nhds_zero_nat]
assert_not_uses Exercises.Analysis.OrderCompleteness.q4_rational_between [exists_rat_btwn]
assert_not_uses Exercises.Analysis.OrderCompleteness.q5_rational_approximation [Rat.denseRange_cast]
assert_not_uses Exercises.Analysis.OrderCompleteness.q6_sup_approximation [lt_csSup_iff]
assert_not_uses Exercises.Analysis.OrderCompleteness.q7_sup_translate [csSup_add]
assert_not_uses Exercises.Analysis.OrderCompleteness.q8_sup_sumset [csSup_add]
assert_not_uses Exercises.Analysis.OrderCompleteness.q10_sSup_sqrtTwoSet_sq_not_lt
  [Real.sq_sqrt, Real.sqrt_sq]
assert_not_uses Exercises.Analysis.OrderCompleteness.q11_sSup_sqrtTwoSet_sq_not_gt
  [Real.sq_sqrt, Real.sqrt_sq]
assert_not_uses Exercises.Analysis.OrderCompleteness.q12_square_root_two_from_supremum
  [Real.sq_sqrt, Real.sqrt_sq]
assert_not_uses Exercises.Analysis.OrderCompleteness.q13_nested_intervals_nonempty
  [Monotone.ciSup_mem_iInter_Icc_of_antitone, ciSup_mem_iInter_Icc_of_antitone_Icc]

assert_not_uses Solutions.Analysis.OrderCompleteness.q2_naturals_unbounded [exists_nat_gt]
assert_not_uses Solutions.Analysis.OrderCompleteness.q3_archimedean_reciprocal
  [tendsto_one_div_atTop_nhds_zero_nat]
assert_not_uses Solutions.Analysis.OrderCompleteness.q4_rational_between [exists_rat_btwn]
assert_not_uses Solutions.Analysis.OrderCompleteness.q5_rational_approximation [Rat.denseRange_cast]
assert_not_uses Solutions.Analysis.OrderCompleteness.q6_sup_approximation [lt_csSup_iff]
assert_not_uses Solutions.Analysis.OrderCompleteness.q7_sup_translate [csSup_add]
assert_not_uses Solutions.Analysis.OrderCompleteness.q8_sup_sumset [csSup_add]
assert_not_uses Solutions.Analysis.OrderCompleteness.q10_sSup_sqrtTwoSet_sq_not_lt
  [Real.sq_sqrt, Real.sqrt_sq]
assert_not_uses Solutions.Analysis.OrderCompleteness.q11_sSup_sqrtTwoSet_sq_not_gt
  [Real.sq_sqrt, Real.sqrt_sq]
assert_not_uses Solutions.Analysis.OrderCompleteness.q12_square_root_two_from_supremum
  [Real.sq_sqrt, Real.sqrt_sq]
assert_not_uses Solutions.Analysis.OrderCompleteness.q13_nested_intervals_nonempty
  [Monotone.ciSup_mem_iInter_Icc_of_antitone, ciSup_mem_iInter_Icc_of_antitone_Icc]
