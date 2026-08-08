import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

/-!
# Exercises — RingTheory / Factorization

Euclidean division supplies greatest common divisors and Bézout identities.  The chain from
Euclidean domains to unique factorization domains explains why irreducible elements are prime in
`ℤ` and in polynomial rings over fields.  Eisenstein's criterion gives a practical route to
irreducibility, while `ℤ[√−5]` shows that factorization need not be unique outside this setting.

Prove each statement yourself; the canonical proofs live in
`Solutions/RingTheory/04Factorization.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.RingTheory.Factorization

open scoped Polynomial

/-! ## Potentially helpful results -/
section

#check EuclideanDomain.gcdA
#check EuclideanDomain.gcdB
#check EuclideanDomain.gcd_eq_gcd_ab
#check EuclideanDomain.div_add_mod
#check UniqueFactorizationMonoid.irreducible_iff_prime
#check eq_zero_or_eq_zero_of_mul_eq_zero

end

/-- **Question 1.**

Bézout's identity expresses a Euclidean gcd as a linear combination.

This is an application exercise: use the two Bézout coefficients supplied by Euclidean division. -/
theorem q1_bezout {R : Type*} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    ∃ x y : R, EuclideanDomain.gcd a b = a * x + b * y := by sorry


/-- **Question 2.**

In a unique factorization domain, irreducible and prime elements coincide.

This is an application exercise: use the irreducible–prime equivalence for unique factorization
domains. -/
theorem q2_irreducible_iff_prime {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R] (a : R) :
    Irreducible a ↔ Prime a := by sorry


/-- **Question 3.**

Euclidean division decomposes a dividend into quotient times divisor plus remainder.

This is an application exercise: use the division-with-remainder identity. -/
theorem q3_division_identity {R : Type*} [EuclideanDomain R] (a b : R) :
    a % b + b * (a / b) = a := by sorry


/-- **Question 4.**

A product of two polynomials over a field is zero only when one of its factors is zero. -/
theorem q4_polynomial_zero_product (K : Type*) [Field K] (p q : K[X]) (hpq : p * q = 0) :
    p = 0 ∨ q = 0 := by sorry


/-- **Question 5.**

Eisenstein's criterion turns a primitive polynomial with the required coefficient divisibility
into an irreducible polynomial.

This is an application exercise: apply Eisenstein's criterion to the supplied hypotheses. -/
theorem q5_eisenstein {f : ℤ[X]} {P : Ideal ℤ} (hE : f.IsEisensteinAt P)
    (hP : P.IsPrime) (hprimitive : f.IsPrimitive) (hdeg : 0 < f.natDegree) : Irreducible f := by sorry


/-- **Question 6.**

The square root of two is irrational.

This is an application exercise: use the irrationality theorem for `√2`. -/
theorem q6_sqrt2_irrational : Irrational (Real.sqrt 2) := by sorry


/-- **Question 7.**

The Euclidean gcd of `12` and `18` is `6`. -/
theorem q7_gcd_12_18 : EuclideanDomain.gcd (12 : ℤ) 18 = 6 := by sorry


/-- **Question 8.**

In `ℤ[√−5]`, `6 = 2·3 = (1 + √−5)(1 - √−5)`, the equality underlying the classical
non-unique-factorization example. -/
theorem q8_zsqrt5_factorization :
    ((6 : ℤ) : ℤ√(-5)) = (2 : ℤ√(-5)) * 3 ∧
      ((6 : ℤ) : ℤ√(-5)) = (⟨1, 1⟩ : ℤ√(-5)) * ⟨1, -1⟩ := by sorry

end Exercises.RingTheory.Factorization
