import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
# Exercises — FieldTheory / Finite Fields

A finite field is not merely a finite collection on which one can add and multiply.  Its prime
field is `𝔽ₚ = ZMod p`, and the whole field is a vector space over that prime field.  Thus a
choice of basis gives coordinates: an element is an `n`-tuple of residues when the basis has `n`
elements, and there are exactly `p^n` such tuples.  This explains why finite fields have
prime-power order.

The multiplicative structure is equally rigid.  In `𝔽₇`, the powers of `3` run through every
nonzero residue, so `3` is a primitive root.  That calculation gives the concrete form of
Fermat's equation `x⁷ = x`.  Finally, characteristic `p` makes the Frobenius operation
`x ↦ x^p` respect addition, while a four-element product ring shows that a prime-power number of
elements alone does not make a ring a field.

Prove each statement yourself; the canonical proofs live in
`Solutions/FieldTheory/02FiniteFields.lean`. Do not commit your proofs into this file.
-/

namespace Exercises.FieldTheory.FiniteFields

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name to see its exact
statement.
-/
section

-- Counting coordinates relative to a basis, and obtaining a basis of a vector space.
#check @Module.card_fintype
#check @VectorSpace.card_fintype

-- The degree of the standard model `GaloisField p n`.
#check @GaloisField.finrank
#check @Module.card_eq_pow_finrank

-- The two algebraic features of the Frobenius operation.
#check @add_pow_char
#check @mul_pow

end


/-- **Question 1.**

Let `F` be a field with a chosen basis of `n` elements over `𝔽ₚ = ZMod p`.  Show that `F` has
`p^n` elements.

Prove without using `FiniteField.card`. -/
theorem q1_card_of_basis (p n : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] (b : Module.Basis (Fin n) (ZMod p) F) :
    Fintype.card F = p ^ n := by
  sorry


/-- **Question 2.**

A finite field containing `𝔽ₚ` has prime-power cardinality: there is an `n` such that it has
`p^n` elements.

Prove without using `FiniteField.card`. -/
theorem q2_card_prime_power (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : ∃ n : ℕ, Fintype.card F = p ^ n := by
  sorry


/-- **Question 3.**

The standard Galois field `GaloisField p n` has degree `n` over `𝔽ₚ`.  Count its elements from
that degree and show that it has `p^n` elements.

Prove without using `GaloisField.card`. -/
theorem q3_galois_field_card (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n := by
  sorry


/-- **Question 4.**

The element `3` is a primitive root modulo `7`: every nonzero residue is a power `3^n` with
`0 ≤ n < 6`. -/
theorem q4_three_generates_f7 (x : ZMod 7) (hx : x ≠ 0) :
    ∃ n : Fin 6, x = (3 : ZMod 7) ^ n.val := by
  sorry


/-- **Question 5.**

Use the preceding primitive-root computation to prove Fermat's equation `x⁷ = x` for every
`x ∈ 𝔽₇`.

Prove without using `ZMod.pow_card`. -/
theorem q5_fermat_f7 (x : ZMod 7) : x ^ 7 = x := by
  sorry


/-- **Question 6.**

If two elements are fixed by Frobenius in a commutative ring of prime characteristic `p`, then
their sum is fixed by Frobenius as well. -/
theorem q6_frobenius_fixed_add (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
    (x y : R) (hx : x ^ p = x) (hy : y ^ p = y) : (x + y) ^ p = x + y := by
  sorry


/-- **Question 7.**

If two elements are fixed by Frobenius in characteristic `p`, then so is their product. -/
theorem q7_frobenius_fixed_mul (p : ℕ) (R : Type*) [CommRing R] [CharP R p]
    (x y : R) (hx : x ^ p = x) (hy : y ^ p = y) : (x * y) ^ p = x * y := by
  sorry


/-- **Question 8.**

The product ring `𝔽₂ × 𝔽₂` has nonzero zero divisors.  Thus a ring can have prime-power
cardinality without being a field. -/
theorem q8_four_elements_not_field :
    ((1 : ZMod 2), (0 : ZMod 2)) * ((0 : ZMod 2), (1 : ZMod 2)) = 0 ∧
      ((1 : ZMod 2), (0 : ZMod 2)) ≠ 0 ∧ ((0 : ZMod 2), (1 : ZMod 2)) ≠ 0 := by
  sorry


/-- **Question 9.**

An element is a *quadratic residue* modulo `p` when it is a square in `𝔽ₚ`.  Show concretely
that `-1` is a quadratic residue modulo `5` but not modulo `3`. -/
theorem q9_neg_one_square_examples :
    IsSquare (-1 : ZMod 5) ∧ ¬ IsSquare (-1 : ZMod 3) := by
  sorry

end Exercises.FieldTheory.FiniteFields
