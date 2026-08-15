import Exercises.GroupTheory.«09FiniteAbelian»
import Solutions.GroupTheory.«09FiniteAbelian»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Finite Abelian Groups

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings against both the
exercise proofs and the shipped canonical solutions.
-/

open Meta

-- Exercise proof (checks the reader's own attempt).
assert_not_uses Exercises.GroupTheory.FiniteAbelian.q5_exponent_attained
  [AddMonoid.exists_addOrderOf_eq_exponent]

-- Solution proof (regression guard on the shipped canonical proof).
assert_not_uses Solutions.GroupTheory.FiniteAbelian.q5_exponent_attained
  [AddMonoid.exists_addOrderOf_eq_exponent]
