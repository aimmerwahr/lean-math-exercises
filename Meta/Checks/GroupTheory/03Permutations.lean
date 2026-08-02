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
