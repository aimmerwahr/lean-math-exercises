import Exercises.GroupTheory.«08Sylow»
import Solutions.GroupTheory.«08Sylow»

import Meta.BanCheck

open Meta

assert_not_uses Solutions.GroupTheory.Sylow.q3_normal_subgroup_order_five
  [Sylow.exists_subgroup_card_pow_prime]
assert_not_uses Solutions.GroupTheory.Sylow.q5_normal_subgroup_order_seven
  [Sylow.exists_subgroup_card_pow_prime]
