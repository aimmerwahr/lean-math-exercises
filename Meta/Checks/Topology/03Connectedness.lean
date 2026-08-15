import Exercises.Topology.«03Connectedness»
import Solutions.Topology.«03Connectedness»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.Topology.Connectedness.q1_indiscrete_connected [isConnected_univ]
assert_not_uses Exercises.Topology.Connectedness.q2_continuous_image_connected [IsConnected.image]
assert_not_uses Exercises.Topology.Connectedness.q3_connected_product [IsConnected.prod]
assert_not_uses Exercises.Topology.Connectedness.q4_quotient_connected [IsConnected.image]
assert_not_uses Exercises.Topology.Connectedness.q5_union_intervals_connected [Set.Icc_union_Icc']
assert_not_uses Exercises.Topology.Connectedness.q6_punctured_interval_disconnected
  [IsPreconnected.ordConnected]
assert_not_uses Exercises.Topology.Connectedness.q7_connected_real_is_interval
  [IsPreconnected.ordConnected]
assert_not_uses Exercises.Topology.Connectedness.q8_intermediate_value
  [intermediate_value_Icc, intermediate_value_Icc']
assert_not_uses Exercises.Topology.Connectedness.q9_sign_change_zero
  [intermediate_value_Icc, intermediate_value_Icc']

assert_not_uses Solutions.Topology.Connectedness.q1_indiscrete_connected [isConnected_univ]
assert_not_uses Solutions.Topology.Connectedness.q2_continuous_image_connected [IsConnected.image]
assert_not_uses Solutions.Topology.Connectedness.q3_connected_product [IsConnected.prod]
assert_not_uses Solutions.Topology.Connectedness.q4_quotient_connected [IsConnected.image]
assert_not_uses Solutions.Topology.Connectedness.q5_union_intervals_connected [Set.Icc_union_Icc']
assert_not_uses Solutions.Topology.Connectedness.q6_punctured_interval_disconnected
  [IsPreconnected.ordConnected]
assert_not_uses Solutions.Topology.Connectedness.q7_connected_real_is_interval
  [IsPreconnected.ordConnected]
assert_not_uses Solutions.Topology.Connectedness.q8_intermediate_value
  [intermediate_value_Icc, intermediate_value_Icc']
assert_not_uses Solutions.Topology.Connectedness.q9_sign_change_zero
  [intermediate_value_Icc, intermediate_value_Icc']
