import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / SpanIndependence

Fix a field `K` and a vector space `V`. The **span** of a set of vectors is the smallest
subspace containing them: it consists precisely of the finite linear combinations of those
vectors. Thus a set spans `V` exactly when its span is all of `V`.

**Linear independence** is the complementary condition. A family is independent when a linear
combination can vanish only when every coefficient vanishes. Equivalently, no vector in the
family can be made from the others. Together, spanning and independence are the two ingredients
of a basis; this sheet develops them before bases and dimension enter the story.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/02SpanIndependence.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project (a proof using a banned lemma, directly or via `simp`/`exact?`, fails the
build).
-/

namespace Exercises.LinearAlgebra.SpanIndependence

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Put a generator into its span, and use the closure of a subspace under the vector-space
-- operations.
#check @Submodule.subset_span
#check @Submodule.add_mem
#check @Submodule.smul_mem
#check @Submodule.span_induction

-- Express independence through coefficient functions or finitely supported coefficient data.
#check @Fintype.linearIndependent_iff
#check @linearIndependent_iff
#check @Finsupp.linearCombination
#check @Finsupp.single
#check @Finsupp.single_ne_zero
#check @linearIndependent_iff_eq_zero_of_smul_mem_span

-- Read a polynomial coefficient after expanding a finite sum of scalar multiples.
#check @Polynomial.finsetSum_coeff
#check @Polynomial.coeff_X_pow
#check @Finset.sum_eq_single

end


/-- **Question 1.**

Show that `(2,5)` belongs to the span of `(1,0)` and `(0,1)` in `ℝ²`. -/
theorem q1_mem_span_explicit : (![2, 5] : Fin 2 → ℝ) ∈
    Submodule.span ℝ {(![1, 0] : Fin 2 → ℝ), ![0, 1]} := by
  sorry


/-- **Question 2.**

For a subspace `W`, prove `span s ≤ W` if and only if every vector of `s` belongs to `W`.

Prove without using `Submodule.span_le`. -/
theorem q2_span_universal (s : Set V) (W : Submodule K V) :
    Submodule.span K s ≤ W ↔ s ⊆ (W : Set V) := by
  sorry


/-- **Question 3.**

If `s ⊆ t`, then `span s ≤ span t`.

Prove without using `Submodule.span_mono`. -/
theorem q3_span_mono {s t : Set V} (h : s ⊆ t) :
    Submodule.span K s ≤ Submodule.span K t := by
  sorry


/-- **Question 4.**

A subspace is already its own span: `span W = W`.

Prove without using `Submodule.span_eq`. -/
theorem q4_span_idempotent (W : Submodule K V) : Submodule.span K (W : Set V) = W := by
  sorry


/-- **Question 5.**

To prove that a family is dependent, one can exhibit a nonzero coefficient function whose linear
combination is zero. Let `δᵢ` be the coefficient function that is `1` at `i` and `0` elsewhere.
First show that `δᵢ` is nonzero. -/
theorem q5_single_nonzero {ι : Type*} (i : ι) : Finsupp.single i (1 : K) ≠ 0 := by
  sorry


/-- **Question 6.**

A family containing the zero vector is linearly dependent. Use the coefficient function from
Question 5: its linear combination with the family vanishes when `v i = 0`. -/
theorem q6_zero_dependent {ι : Type*} (v : ι → V) (i : ι) (hvi : v i = 0) :
    ¬ LinearIndependent K v := by
  sorry


/-- **Question 7.**

A finite family is linearly dependent if and only if one of its vectors lies in the span of all
the others.

Prove without using `linearIndependent_iff_notMem_span`. -/
theorem q7_dependent_mem_span {n : ℕ} (v : Fin (n + 1) → V) :
    ¬ LinearIndependent K v ↔ ∃ i, v i ∈ Submodule.span K (v '' {j | j ≠ i}) := by
  sorry


/-- **Question 8.**

To prove independence of the powers of `X`, extract the coefficient of `Xⁱ` from a vanishing
linear combination. Show that if
`∑ j, c j • Xʲ = 0`, then the coefficient `c i` is zero. -/
theorem q8_polynomial_coeff_zero {n : ℕ} (c : Fin (n + 1) → K)
    (hc : ∑ j, c j • (Polynomial.X : Polynomial K) ^ j.val = 0) (i : Fin (n + 1)) : c i = 0 := by
  sorry


/-- **Question 9.**

For every `n`, the polynomials `1, X, X², …, Xⁿ` are linearly independent in `K[X]`.

Here `X` is the polynomial indeterminate, so the family is indexed by the exponents
`0, 1, …, n`.

Prove without using `Polynomial.basisMonomials`. -/
theorem q9_polynomials_independent {n : ℕ} : LinearIndependent K
    (fun i : Fin (n + 1) => (Polynomial.X : Polynomial K) ^ i.val) := by
  sorry

end Exercises.LinearAlgebra.SpanIndependence
