import Exercises.GroupTheory.«06Quotients»
import Solutions.GroupTheory.«06Quotients»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Normal Subgroups & Quotients

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings against both the
exercise proofs and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.GroupTheory.Quotients.q2_index_two_normal [Subgroup.normal_of_index_eq_two]
assert_not_uses Exercises.GroupTheory.Quotients.q3_first_iso [QuotientGroup.quotientKerEquivRange]
assert_not_uses Exercises.GroupTheory.Quotients.q4_normal_iff_kernel [MonoidHom.normal_ker, QuotientGroup.ker_mk']
assert_not_uses Exercises.GroupTheory.Quotients.q5_third_iso [QuotientGroup.quotientQuotientEquivQuotient]
assert_not_uses Exercises.GroupTheory.Quotients.q6_commutator_le_ker [Abelianization.commutator_subset_ker]
assert_not_uses Exercises.GroupTheory.Quotients.q7_abelianization [Abelianization.lift]
assert_not_uses Exercises.GroupTheory.Quotients.q9_quotient_trivial [QuotientGroup.quotientBot, QuotientGroup.subsingleton_quotient_top]
assert_not_uses Exercises.GroupTheory.Quotients.q10_quotient_center_cyclic_abelian [isMulCommutative_of_isCyclic_quotient_center_self]
assert_not_uses Exercises.GroupTheory.Quotients.q10_quotient_center_cyclic_abelian
  [MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.GroupTheory.Quotients.q2_index_two_normal [Subgroup.normal_of_index_eq_two]
assert_not_uses Solutions.GroupTheory.Quotients.q3_first_iso [QuotientGroup.quotientKerEquivRange]
assert_not_uses Solutions.GroupTheory.Quotients.q4_normal_iff_kernel [MonoidHom.normal_ker, QuotientGroup.ker_mk']
assert_not_uses Solutions.GroupTheory.Quotients.q5_third_iso [QuotientGroup.quotientQuotientEquivQuotient]
assert_not_uses Solutions.GroupTheory.Quotients.q6_commutator_le_ker [Abelianization.commutator_subset_ker]
assert_not_uses Solutions.GroupTheory.Quotients.q7_abelianization [Abelianization.lift]
assert_not_uses Solutions.GroupTheory.Quotients.q9_quotient_trivial [QuotientGroup.quotientBot, QuotientGroup.subsingleton_quotient_top]
assert_not_uses Solutions.GroupTheory.Quotients.q10_quotient_center_cyclic_abelian [isMulCommutative_of_isCyclic_quotient_center_self]
assert_not_uses Solutions.GroupTheory.Quotients.q10_quotient_center_cyclic_abelian
  [MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center]
