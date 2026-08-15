import Exercises.Topology.«02Compactness»
import Solutions.Topology.«02Compactness»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Topology.Compactness.q1_finite_compact [Set.Finite.isCompact]
assert_not_uses Exercises.Topology.Compactness.q2_closed_interval_compact [isCompact_Icc]
assert_not_uses Exercises.Topology.Compactness.q3_compact_image [IsCompact.image_of_continuousOn]
assert_not_uses Exercises.Topology.Compactness.q4_extreme_value
  [IsCompact.exists_isMaxOn, IsCompact.exists_isMinOn]
assert_not_uses Exercises.Topology.Compactness.q5_uniform_continuity_compact
  [IsCompact.uniformContinuousOn_of_continuous, CompactSpace.uniformContinuous_of_continuous]
assert_not_uses Exercises.Topology.Compactness.q6_real_compact_neighborhood
  [LocallyCompactSpace.local_compact_nhds, locallyCompact_of_proper]

assert_not_uses Solutions.Topology.Compactness.q1_finite_compact [Set.Finite.isCompact]
assert_not_uses Solutions.Topology.Compactness.q2_closed_interval_compact [isCompact_Icc]
assert_not_uses Solutions.Topology.Compactness.q3_compact_image [IsCompact.image_of_continuousOn]
assert_not_uses Solutions.Topology.Compactness.q4_extreme_value
  [IsCompact.exists_isMaxOn, IsCompact.exists_isMinOn]
assert_not_uses Solutions.Topology.Compactness.q5_uniform_continuity_compact
  [IsCompact.uniformContinuousOn_of_continuous, CompactSpace.uniformContinuous_of_continuous]
assert_not_uses Solutions.Topology.Compactness.q6_real_compact_neighborhood
  [LocallyCompactSpace.local_compact_nhds, locallyCompact_of_proper]
