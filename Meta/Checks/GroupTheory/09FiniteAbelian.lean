import Exercises.GroupTheory.«09FiniteAbelian»
import Solutions.GroupTheory.«09FiniteAbelian»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.GroupTheory.FiniteAbelian.q5_exponent_attained
  [AddMonoid.exists_addOrderOf_eq_exponent]
assert_not_uses Solutions.GroupTheory.FiniteAbelian.q5_exponent_attained
  [AddMonoid.exists_addOrderOf_eq_exponent]
