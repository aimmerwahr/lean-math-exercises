import Exercises.Topology.«01MetricSpaces»
import Solutions.Topology.«01MetricSpaces»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Topology.MetricSpaces.q1_open_ball [Metric.isOpen_ball]
assert_not_uses Exercises.Topology.MetricSpaces.q2_unique_limit [tendsto_nhds_unique]
assert_not_uses Exercises.Topology.MetricSpaces.q3_continuous_iff_seqContinuous
  [continuous_iff_seqContinuous]
assert_not_uses Exercises.Topology.MetricSpaces.q4_abs_lipschitz [continuous_abs]
assert_not_uses Exercises.Topology.MetricSpaces.q5_square_continuous_at
  [continuousAt_pow, continuous_pow]
assert_not_uses Exercises.Topology.MetricSpaces.q6_uniform_continuous_cauchy
  [UniformContinuous.comp_cauchySeq]

assert_not_uses Solutions.Topology.MetricSpaces.q1_open_ball [Metric.isOpen_ball]
assert_not_uses Solutions.Topology.MetricSpaces.q2_unique_limit [tendsto_nhds_unique]
assert_not_uses Solutions.Topology.MetricSpaces.q3_continuous_iff_seqContinuous
  [continuous_iff_seqContinuous]
assert_not_uses Solutions.Topology.MetricSpaces.q4_abs_lipschitz [continuous_abs]
assert_not_uses Solutions.Topology.MetricSpaces.q5_square_continuous_at
  [continuousAt_pow, continuous_pow]
assert_not_uses Solutions.Topology.MetricSpaces.q6_uniform_continuous_cauchy
  [UniformContinuous.comp_cauchySeq]
