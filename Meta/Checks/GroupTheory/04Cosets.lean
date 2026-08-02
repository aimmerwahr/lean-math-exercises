import Exercises.GroupTheory.«04Cosets»
import Solutions.GroupTheory.«04Cosets»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Cosets

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against both the exercise
proofs the reader writes and the shipped solution proofs.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.GroupTheory.Cosets.q2_lagrange [Subgroup.card_subgroup_dvd_card]
assert_not_uses Exercises.GroupTheory.Cosets.q3_orderOf_dvd_card [orderOf_dvd_card]
assert_not_uses Exercises.GroupTheory.Cosets.q4_prime_order_cyclic [isCyclic_of_prime_card]
assert_not_uses Exercises.GroupTheory.Cosets.q5_fermat_little [ZMod.pow_card_sub_one_eq_one]
assert_not_uses Exercises.GroupTheory.Cosets.q6_euler [ZMod.pow_totient]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.GroupTheory.Cosets.q2_lagrange [Subgroup.card_subgroup_dvd_card]
assert_not_uses Solutions.GroupTheory.Cosets.q3_orderOf_dvd_card [orderOf_dvd_card]
assert_not_uses Solutions.GroupTheory.Cosets.q4_prime_order_cyclic [isCyclic_of_prime_card]
assert_not_uses Solutions.GroupTheory.Cosets.q5_fermat_little [ZMod.pow_card_sub_one_eq_one]
assert_not_uses Solutions.GroupTheory.Cosets.q6_euler [ZMod.pow_totient]
