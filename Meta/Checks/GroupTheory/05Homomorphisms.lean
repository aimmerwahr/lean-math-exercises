import Exercises.GroupTheory.«05Homomorphisms»
import Solutions.GroupTheory.«05Homomorphisms»
import Meta.BanCheck

/-!
# Internal ban checks — GroupTheory / Homomorphisms & Isomorphisms

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings against both the
exercise proofs and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.GroupTheory.Homomorphisms.q2_injective_iff_ker [MonoidHom.ker_eq_bot_iff]
assert_not_uses Exercises.GroupTheory.Homomorphisms.q3_ker_normal [MonoidHom.normal_ker]
assert_not_uses Exercises.GroupTheory.Homomorphisms.q4_cayley [MulAction.toPermHom]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.GroupTheory.Homomorphisms.q2_injective_iff_ker [MonoidHom.ker_eq_bot_iff]
assert_not_uses Solutions.GroupTheory.Homomorphisms.q3_ker_normal [MonoidHom.normal_ker]
assert_not_uses Solutions.GroupTheory.Homomorphisms.q4_cayley [MulAction.toPermHom]
