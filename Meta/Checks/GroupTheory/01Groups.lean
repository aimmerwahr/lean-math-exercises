import Exercises.GroupTheory.«01Groups»
import Solutions.GroupTheory.«01Groups»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Groups

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against two targets:

* the **exercise** proofs you write in `Exercises/GroupTheory/01Groups.lean` — building the project
  fails here if your proof uses a banned lemma (directly or via `simp`/`omega`/`decide`); while an
  exercise is still `sorry` its check is a no-op;
* the **solution** proofs in `Solutions/GroupTheory/01Groups.lean` — a permanent regression guard that
  the shipped solutions keep respecting the bans.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.GroupTheory.Groups.q2_inv_mul_rev [mul_inv_rev]
assert_not_uses Exercises.GroupTheory.Groups.q3_center_isSubgroup [Subgroup.center]
assert_not_uses Exercises.GroupTheory.Groups.q9_subgroup_inter_glb
  [Subgroup.instCompleteLattice, Subgroup.instInfSet]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.GroupTheory.Groups.q2_inv_mul_rev [mul_inv_rev]
assert_not_uses Solutions.GroupTheory.Groups.q3_center_isSubgroup [Subgroup.center]
assert_not_uses Solutions.GroupTheory.Groups.q9_subgroup_inter_glb
  [Subgroup.instCompleteLattice, Subgroup.instInfSet]
