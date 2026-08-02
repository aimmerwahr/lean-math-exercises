import Exercises.RingTheory.«01Rings»
import Solutions.RingTheory.«01Rings»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.Rings.q3_char_prime_or_zero [CharP.char_is_prime_or_zero]
assert_not_uses Exercises.RingTheory.Rings.q6_finite_domain_units [IsLeftRegular.isUnit_of_finite]
assert_not_uses Exercises.RingTheory.Rings.q14_gaussian_units_exactly_four [Zsqrtd.norm_eq_one_iff']
assert_not_uses Solutions.RingTheory.Rings.q3_char_prime_or_zero [CharP.char_is_prime_or_zero]
assert_not_uses Solutions.RingTheory.Rings.q6_finite_domain_units [IsLeftRegular.isUnit_of_finite]
assert_not_uses Solutions.RingTheory.Rings.q14_gaussian_units_exactly_four [Zsqrtd.norm_eq_one_iff']
