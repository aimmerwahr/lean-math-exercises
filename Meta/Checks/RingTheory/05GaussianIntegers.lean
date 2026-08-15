import Exercises.RingTheory.«05GaussianIntegers»
import Solutions.RingTheory.«05GaussianIntegers»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.GaussianIntegers.q1_conjugate_norm_product
  [Zsqrtd.norm_mul]
assert_not_uses Exercises.RingTheory.GaussianIntegers.q2_norm_prime_irreducible
  [Zsqrtd.norm_mul, Zsqrtd.norm_eq_one_iff']
assert_not_uses Solutions.RingTheory.GaussianIntegers.q1_conjugate_norm_product
  [Zsqrtd.norm_mul]

assert_not_uses Solutions.RingTheory.GaussianIntegers.q2_norm_prime_irreducible
  [Zsqrtd.norm_mul, Zsqrtd.norm_eq_one_iff']
