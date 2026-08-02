import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

namespace Solutions.RingTheory.Factorization

open scoped Polynomial

theorem q1_bezout {R : Type*} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    ∃ x y : R, EuclideanDomain.gcd a b = a * x + b * y := by
  exact ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, EuclideanDomain.gcd_eq_gcd_ab a b⟩

theorem q2_irreducible_iff_prime {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R] (a : R) :
    Irreducible a ↔ Prime a := by
  exact UniqueFactorizationMonoid.irreducible_iff_prime

theorem q3_division_identity {R : Type*} [EuclideanDomain R] (a b : R) :
    a % b + b * (a / b) = a := by
  simpa [mul_comm, add_comm] using EuclideanDomain.div_add_mod a b

theorem q4_polynomial_domain (K : Type*) [Field K] : IsDomain K[X] := by
  infer_instance

theorem q5_eisenstein {f : ℤ[X]} {P : Ideal ℤ} (hE : f.IsEisensteinAt P)
    (hP : P.IsPrime) (hprimitive : f.IsPrimitive) (hdeg : 0 < f.natDegree) : Irreducible f := by
  exact hE.irreducible hP hprimitive hdeg

theorem q6_sqrt2_irrational : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

theorem q7_gcd_12_18 : EuclideanDomain.gcd (12 : ℤ) 18 = 6 := by
  norm_num [EuclideanDomain.gcd]

theorem q8_zsqrt5_factorization :
    ((6 : ℤ) : ℤ√(-5)) = (2 : ℤ√(-5)) * 3 ∧
      ((6 : ℤ) : ℤ√(-5)) = (⟨1, 1⟩ : ℤ√(-5)) * ⟨1, -1⟩ := by
  constructor <;> ext <;> norm_num

end Solutions.RingTheory.Factorization
