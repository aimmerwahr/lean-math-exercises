import Exercises.RingTheory.«03Polynomials»
import Solutions.RingTheory.«03Polynomials»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.Polynomials.q2_factor_theorem [Polynomial.dvd_iff_isRoot]
assert_not_uses Exercises.RingTheory.Polynomials.q5_roots_le_degree [Polynomial.card_roots']

assert_not_uses Solutions.RingTheory.Polynomials.q2_factor_theorem [Polynomial.dvd_iff_isRoot]
assert_not_uses Solutions.RingTheory.Polynomials.q5_roots_le_degree [Polynomial.card_roots']
