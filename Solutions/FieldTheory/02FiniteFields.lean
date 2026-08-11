import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

namespace Solutions.FieldTheory.FiniteFields

theorem q1_card_of_basis (p n : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] (b : Module.Basis (Fin n) (ZMod p) F) :
    Fintype.card F = p ^ n := by
  -- Coordinates in the basis identify `F` with the functions `Fin n → 𝔽ₚ`.
  -- There are `p` choices in each of the `n` coordinates.
  rw [Module.card_fintype b, Fintype.card_fin, ZMod.card]


theorem q2_card_prime_power (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : ∃ n : ℕ, Fintype.card F = p ^ n := by
  -- Choose a basis over the prime field and count its coordinate functions.
  obtain ⟨n, hn⟩ := VectorSpace.card_fintype (ZMod p) F
  exact ⟨n, by simpa only [ZMod.card] using hn⟩


theorem q3_galois_field_card (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n := by
  -- This field has an `n`-element basis over `𝔽ₚ`, so the coordinate count from Q1 is `p^n`.
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card,
    GaloisField.finrank p hn]


theorem q4_three_generates_f7 (x : ZMod 7) (hx : x ≠ 0) :
    ∃ n : Fin 6, x = (3 : ZMod 7) ^ n.val := by
  -- Every residue has a representative from 0 through 6.  Direct computation identifies each
  -- nonzero representative with the appropriate power of 3.
  have hval : x.val < 7 := x.val_lt
  rw [← ZMod.natCast_zmod_val x]
  interval_cases h : x.val
  · exfalso
    apply hx
    rw [← ZMod.natCast_zmod_val x, h]
    rfl
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨3, by decide⟩


theorem q5_fermat_f7 (x : ZMod 7) : x ^ 7 = x := by
  -- Zero is fixed immediately.  Otherwise Q4 writes `x` as a power of `3`; the six possible
  -- exponents can then be checked against the completed power cycle.
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn⟩ := q4_three_generates_f7 x hx
  rw [hn]
  fin_cases n <;> decide


theorem q6_frobenius_fixed_add (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
    (x y : R) (hx : x ^ p = x) (hy : y ^ p = y) : (x + y) ^ p = x + y := by
  -- All mixed binomial terms have coefficients divisible by the characteristic, leaving only the
  -- two endpoint terms, which are `x` and `y` by hypothesis.
  rw [add_pow_char x y p, hx, hy]


theorem q7_frobenius_fixed_mul (p : ℕ) (R : Type*) [CommRing R] [CharP R p]
    (x y : R) (hx : x ^ p = x) (hy : y ^ p = y) : (x * y) ^ p = x * y := by
  -- Frobenius sends a product to the product of the two Frobenius values.
  rw [mul_pow, hx, hy]


theorem q8_four_elements_not_field :
    ((1 : ZMod 2), (0 : ZMod 2)) * ((0 : ZMod 2), (1 : ZMod 2)) = 0 ∧
      ((1 : ZMod 2), (0 : ZMod 2)) ≠ 0 ∧ ((0 : ZMod 2), (1 : ZMod 2)) ≠ 0 := by
  -- The two coordinate axes contain nonzero elements whose product is zero.
  norm_num


theorem q9_neg_one_square_examples :
    IsSquare (-1 : ZMod 5) ∧ ¬ IsSquare (-1 : ZMod 3) := by
  constructor
  · exact ⟨2, by decide⟩
  · rintro ⟨x, hx⟩
    -- The three representatives modulo 3 have squares 0, 1, and 1, never `-1`.
    have hval : x.val < 3 := x.val_lt
    rw [← ZMod.natCast_zmod_val x] at hx
    interval_cases h : x.val
    · have hne : (-1 : ZMod 3) ≠ 0 := by decide
      exact hne (by simpa [h] using hx)
    · have hne : (-1 : ZMod 3) ≠ 1 := by decide
      exact hne (by simpa [h] using hx)
    · have hsq : ((2 : ℕ) : ZMod 3) * ((2 : ℕ) : ZMod 3) = 1 := by decide
      exact (by decide : (-1 : ZMod 3) ≠ 1) (hx.trans hsq)

end Solutions.FieldTheory.FiniteFields
