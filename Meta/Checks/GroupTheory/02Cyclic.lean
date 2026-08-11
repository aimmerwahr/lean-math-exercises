import Exercises.GroupTheory.«02Cyclic»
import Solutions.GroupTheory.«02Cyclic»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Cyclic

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against both the exercise
proofs the reader writes and the shipped solution proofs.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.GroupTheory.Cyclic.q2_orderOf_pow [orderOf_pow]
assert_not_uses Exercises.GroupTheory.Cyclic.q5_subgroup_isCyclic [Subgroup.isCyclic]
assert_not_uses Exercises.GroupTheory.Cyclic.q6_unique_subgroup_per_divisor [Subgroup.isCyclic]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.GroupTheory.Cyclic.q2_orderOf_pow [orderOf_pow]
assert_not_uses Solutions.GroupTheory.Cyclic.q5_subgroup_isCyclic [Subgroup.isCyclic]
assert_not_uses Solutions.GroupTheory.Cyclic.q6_unique_subgroup_per_divisor [Subgroup.isCyclic]
