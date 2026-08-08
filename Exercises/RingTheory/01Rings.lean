import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Exercises — RingTheory / Rings, Domains & Fields

A commutative ring combines addition with a distributive multiplication. Units are the elements
that can be divided by; zero divisors obstruct cancellation. Integral domains have no such
obstruction, and the characteristic records the additive period of the multiplicative identity.

Prove each statement yourself; canonical proofs live in `Solutions/RingTheory/01Rings.lean`.
-/

namespace Exercises.RingTheory.Rings

variable {R : Type*} [CommRing R]

/-- The real Hamilton quaternions written as coordinate tuples `a + bi + cj + dk`.

This small model exposes the multiplication and inverse formula used below, rather than hiding
them behind a pre-existing division-ring instance. -/
@[ext]
structure Hamilton where
  re : ℝ
  i : ℝ
  j : ℝ
  k : ℝ

namespace Hamilton

/-- The additive and multiplicative identities in the coordinate model. -/
def zero : Hamilton := ⟨0, 0, 0, 0⟩
def one : Hamilton := ⟨1, 0, 0, 0⟩

/-- Hamilton's multiplication rule, determined by `i² = j² = k² = ijk = -1`. -/
def mul (q r : Hamilton) : Hamilton :=
  ⟨q.re * r.re - q.i * r.i - q.j * r.j - q.k * r.k,
    q.re * r.i + q.i * r.re + q.j * r.k - q.k * r.j,
    q.re * r.j - q.i * r.k + q.j * r.re + q.k * r.i,
    q.re * r.k + q.i * r.j - q.j * r.i + q.k * r.re⟩

/-- Quaternion conjugation sends `a + bi + cj + dk` to `a - bi - cj - dk`. -/
def conj (q : Hamilton) : Hamilton := ⟨q.re, -q.i, -q.j, -q.k⟩

/-- The squared norm `a² + b² + c² + d²`. -/
def normSq (q : Hamilton) : ℝ := q.re ^ 2 + q.i ^ 2 + q.j ^ 2 + q.k ^ 2

/-- Multiply every coordinate of a quaternion by a real scalar. -/
def scale (t : ℝ) (q : Hamilton) : Hamilton := ⟨t * q.re, t * q.i, t * q.j, t * q.k⟩

/-- The candidate inverse `q̄ / ‖q‖²` for a nonzero quaternion. -/
noncomputable def inv (q : Hamilton) : Hamilton := scale (normSq q)⁻¹ (conj q)

/-- Additive negation in the coordinate model. -/
def neg (q : Hamilton) : Hamilton := ⟨-q.re, -q.i, -q.j, -q.k⟩

/-- The basic quaternion unit `i`. -/
def qi : Hamilton := ⟨0, 1, 0, 0⟩

/-- The basic quaternion unit `j`. -/
def qj : Hamilton := ⟨0, 0, 1, 0⟩

end Hamilton

/-- A candidate integer scalar action on an abelian group.  Additivity in the integer variable,
together with the values at `0` and `1`, expresses repeated addition without using a module
instance. -/
def IsIntScalarAction {A : Type*} [AddCommGroup A] (act : ℤ → A → A) : Prop :=
  (∀ a, act 0 a = 0) ∧ (∀ a, act 1 a = a) ∧
    ∀ m n a, act (m + n) a = act m a + act n a

/-! ## Potentially helpful results -/
section

-- Basic ring identities and cancellation.
#check neg_mul
#check IsUnit
#check CharP.cast_eq_zero_iff
#check isUnit_iff_exists

-- Residues, divisibility, and finite maps.
#check Nat.Prime.dvd_mul
#check ZMod.natCast_eq_zero_iff
#check ZMod.natCast_zmod_surjective
#check ZMod.isUnit_iff_coprime
#check Finite.surjective_of_injective

-- Norm arguments for Gaussian integers.
#check Zsqrtd.norm_mul
#check Zsqrtd.norm_def
#check Zsqrtd.norm_nonneg
#check GaussianInt.norm_eq_zero
#check Int.eq_one_of_dvd_one

-- Induction over positive and negative integers.
#check Int.induction_on

end

/-- **Question 1.** Negation distributes across multiplication on the left. -/
theorem q1_neg_mul (a b : R) : (-a) * b = -(a * b) := by sorry


/-- **Question 2.** A unit cannot be a zero divisor: if `a` is a unit and `a*b = 0`, then `b = 0`. -/
theorem q2_unit_not_zero_divisor {a b : R} (ha : IsUnit a) (hab : a * b = 0) : b = 0 := by sorry


/-- **Question 3.** In a ring of characteristic `p`, the characteristic is either prime or zero. -/
theorem q3_char_prime_or_zero (p : ℕ) [IsDomain R] [CharP R p] : p.Prime ∨ p = 0 := by sorry


/-- **Question 4.** The residue class of `5` is a unit modulo `12`. -/
theorem q4_zmod12_unit : IsUnit (5 : ZMod 12) := by sorry


/-- **Question 5.** The integers are initial among rings: every ring homomorphism from `ℤ` to `R`
is the canonical integer-cast homomorphism. -/
theorem q5_int_initial (f : ℤ →+* R) : f = Int.castRingHom R := by sorry


/-- **Question 6.** Every nonzero element of a finite integral domain is a unit. -/
theorem q6_finite_domain_units [Finite R] [IsDomain R] {a : R} (ha : a ≠ 0) : IsUnit a := by sorry


/-- **Question 7.** Modulo `12`, the class of `2` is a nonzero zero divisor and therefore not a
unit. -/
theorem q7_zmod12_two_zero_divisor :
    ¬ IsUnit (2 : ZMod 12) ∧ (2 : ZMod 12) * 6 = 0 ∧ (6 : ZMod 12) ≠ 0 := by sorry


/-- **Question 8.** A residue class modulo `12` is a unit exactly when one (equivalently, every)
integer representative is coprime to `12`. -/
theorem q8_zmod12_unit_iff (a : ZMod 12) :
    IsUnit a ↔ ∃ n : ℕ, a = n ∧ n.Coprime 12 := by sorry


/-- **Question 9.** In a Boolean ring (one satisfying `x² = x` for every `x`), every element has
additive order dividing two, and multiplication is commutative. -/
theorem q9_boolean_two_torsion_and_comm {S : Type*} [Ring S]
    (h : ∀ x : S, x * x = x) (a b : S) : a + a = 0 ∧ a * b = b * a := by sorry


/-- **Question 10.** The Gaussian integers `ℤ[i]` have no zero divisors: if `zw = 0`, then
`z = 0` or `w = 0`. -/
theorem q10_gaussian_no_zero_divisors (z w : GaussianInt) (hzw : z * w = 0) : z = 0 ∨ w = 0 := by
  sorry


/-- **Question 11.** In the coordinate model of the real quaternions, every nonzero quaternion
has a displayed two-sided inverse.  The basic units `i` and `j` also anticommute, so quaternion
multiplication is not commutative. -/
theorem q11_hamilton_inverse_and_noncommutative (q : Hamilton) (hq : q ≠ Hamilton.zero) :
    (∃ r, Hamilton.mul q r = Hamilton.one ∧ Hamilton.mul r q = Hamilton.one) ∧
      Hamilton.mul Hamilton.qi Hamilton.qj = Hamilton.neg (Hamilton.mul Hamilton.qj Hamilton.qi) := by
  sorry


/-- **Question 12.** An integer scalar action on an abelian group is forced to be repeated
addition: any action additive in the integer variable and taking `1 • a = a` agrees with the
usual integer multiple `n • a`. -/
theorem q12_int_scalar_action_unique {A : Type*} [AddCommGroup A] (act : ℤ → A → A)
    (hact : IsIntScalarAction act) (n : ℤ) (a : A) : act n a = n • a := by sorry


/-- **Question 13.** For `n ≥ 2`, the residue ring `ℤ/nℤ` has no zero divisors exactly when
`n` is prime. -/
theorem q13_zmod_no_zero_divisors_iff_prime (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a b : ZMod n, a * b = 0 → a = 0 ∨ b = 0 := by sorry


/-- **Question 14.** The only units of the Gaussian integers are `1`, `-1`, `i`, and `-i`.
Here `i` and `-i` are represented by the coordinate pairs `⟨0, 1⟩` and `⟨0, -1⟩`.

Prove without using `Zsqrtd.norm_eq_one_iff'`. -/
theorem q14_gaussian_units_exactly_four (z : GaussianInt) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ := by sorry

end Exercises.RingTheory.Rings
