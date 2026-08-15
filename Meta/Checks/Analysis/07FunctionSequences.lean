import Exercises.Analysis.«07FunctionSequences»
import Solutions.Analysis.«07FunctionSequences»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Analysis.FunctionSequences.q6_geometric_series_continuous
  [ContinuousOn.div]
assert_not_uses Solutions.Analysis.FunctionSequences.q6_geometric_series_continuous
  [ContinuousOn.div]

assert_not_uses Exercises.Analysis.FunctionSequences.q8_abs_not_differentiable_at_zero
  [not_differentiableAt_abs_zero]
assert_not_uses Solutions.Analysis.FunctionSequences.q8_abs_not_differentiable_at_zero
  [not_differentiableAt_abs_zero]
