import Exercises.GroupTheory.«05Homomorphisms»
import Solutions.GroupTheory.«05Homomorphisms»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.GroupTheory.Homomorphisms.q2_injective_iff_ker [MonoidHom.ker_eq_bot_iff]
assert_not_uses Exercises.GroupTheory.Homomorphisms.q3_ker_normal [MonoidHom.normal_ker]
assert_not_uses Exercises.GroupTheory.Homomorphisms.q4_cayley [MulAction.toPermHom]
assert_not_uses Solutions.GroupTheory.Homomorphisms.q2_injective_iff_ker [MonoidHom.ker_eq_bot_iff]
assert_not_uses Solutions.GroupTheory.Homomorphisms.q3_ker_normal [MonoidHom.normal_ker]
assert_not_uses Solutions.GroupTheory.Homomorphisms.q4_cayley [MulAction.toPermHom]
