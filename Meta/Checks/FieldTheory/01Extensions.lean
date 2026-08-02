import Exercises.FieldTheory.«01Extensions»
import Solutions.FieldTheory.«01Extensions»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.FieldTheory.Extensions.q1_complex_coordinates [Complex.finrank_real_complex]
assert_not_uses Exercises.FieldTheory.Extensions.q8_base_generated_by_one [Module.finrank_self]

assert_not_uses Solutions.FieldTheory.Extensions.q1_complex_coordinates [Complex.finrank_real_complex]
assert_not_uses Solutions.FieldTheory.Extensions.q8_base_generated_by_one [Module.finrank_self]
