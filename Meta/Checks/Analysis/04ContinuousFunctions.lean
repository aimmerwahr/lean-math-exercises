import Exercises.Analysis.«04ContinuousFunctions»
import Solutions.Analysis.«04ContinuousFunctions»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Analysis.ContinuousFunctions.q1_matching_piecewise_continuous
  [continuous_if_le, Continuous.if_le]
assert_not_uses Exercises.Analysis.ContinuousFunctions.q3_interval_self_map_fixed_point
  [exists_mem_Icc_isFixedPt]

assert_not_uses Solutions.Analysis.ContinuousFunctions.q1_matching_piecewise_continuous
  [continuous_if_le, Continuous.if_le]
assert_not_uses Solutions.Analysis.ContinuousFunctions.q3_interval_self_map_fixed_point
  [exists_mem_Icc_isFixedPt]
