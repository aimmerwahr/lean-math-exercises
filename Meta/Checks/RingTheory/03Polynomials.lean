import Exercises.RingTheory.«03Polynomials»
import Solutions.RingTheory.«03Polynomials»
import Meta.BanCheck

open Meta

assert_not_uses Exercises.RingTheory.Polynomials.q1_factor_theorem
  [Polynomial.dvd_iff_isRoot, Polynomial.mul_divByMonic_eq_iff_isRoot]

assert_not_uses Solutions.RingTheory.Polynomials.q1_factor_theorem
  [Polynomial.dvd_iff_isRoot, Polynomial.mul_divByMonic_eq_iff_isRoot]
