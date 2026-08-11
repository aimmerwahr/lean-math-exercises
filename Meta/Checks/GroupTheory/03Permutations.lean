import Exercises.GroupTheory.«03Permutations»
import Solutions.GroupTheory.«03Permutations»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Permutations

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against both the exercise
proofs the reader writes and the shipped solution proofs.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.GroupTheory.Permutations.q4_swaps_generate [Equiv.Perm.closure_isSwap]
assert_not_uses Exercises.GroupTheory.Permutations.q6_alternating_index_two [alternatingGroup.index_eq_two]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.GroupTheory.Permutations.q4_swaps_generate [Equiv.Perm.closure_isSwap]
assert_not_uses Solutions.GroupTheory.Permutations.q6_alternating_index_two [alternatingGroup.index_eq_two]

-- The concrete computations must expose their coordinate and sign arguments rather than defer to
-- the decision procedure.
assert_not_uses Solutions.GroupTheory.Permutations.q1_swap_product [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q2_sign_swap [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q3_sign_cycle_length [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q5_three_cycle_even [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q7_order_eq_lcm [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q8_cycle_decomp_concrete [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q9_fifteen_puzzle_parity [of_decide_eq_true]
assert_not_uses Solutions.GroupTheory.Permutations.q10_square_dihedral_relations [of_decide_eq_true]
