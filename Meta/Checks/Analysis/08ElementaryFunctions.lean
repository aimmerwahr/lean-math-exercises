import Exercises.Analysis.«08ElementaryFunctions»
import Solutions.Analysis.«08ElementaryFunctions»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Analysis.ElementaryFunctions.q1_exp_tangent_bound [Real.add_one_le_exp]
assert_not_uses Exercises.Analysis.ElementaryFunctions.q2_log_tangent_bound
  [Real.log_le_sub_one_of_pos]
assert_not_uses Exercises.Analysis.ElementaryFunctions.q3_sin_lipschitz
  [Real.abs_sin_le_abs, Real.abs_sin_sub_sin_le, Real.lipschitzWith_sin]
assert_not_uses Exercises.Analysis.ElementaryFunctions.q4_cos_quadratic_bound
  [Real.one_sub_sq_div_two_le_cos, Real.cos_le_one]

assert_not_uses Solutions.Analysis.ElementaryFunctions.q2_log_tangent_bound
  [Real.log_le_sub_one_of_pos]
assert_not_uses Solutions.Analysis.ElementaryFunctions.q3_sin_lipschitz
  [Real.abs_sin_le_abs, Real.abs_sin_sub_sin_le, Real.lipschitzWith_sin]
assert_not_uses Solutions.Analysis.ElementaryFunctions.q4_cos_quadratic_bound
  [Real.one_sub_sq_div_two_le_cos, Real.cos_le_one]
assert_not_uses Solutions.Analysis.ElementaryFunctions.q1_exp_tangent_bound [Real.add_one_le_exp]
