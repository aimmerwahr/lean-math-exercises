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
#check @Finsupp.mapDomain_injective

-- Read a polynomial coefficient after expanding a finite sum of scalar multiples.
#check @Polynomial.finsetSum_coeff
#check @Polynomial.coeff_X_pow

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

A family containing the zero vector is linearly dependent. -/
theorem q5_zero_dependent {ι : Type*} (v : ι → V) (i : ι) (hvi : v i = 0) :
    ¬ LinearIndependent K v := by
  sorry

/-- **Question 6.**

The one-vector family `(v)` is linearly independent if and only if `v ≠ 0`.

Prove without using `linearIndependent_unique_iff`. -/
theorem q6_singleton_independent (v : V) : LinearIndependent K ![v] ↔ v ≠ 0 := by
  sorry

/-- **Question 7.**

If `(vᵢ)` is linearly independent and `f` is injective, then the subfamily `(v_(f j))` is
linearly independent.

Prove without using `LinearIndependent.comp`. -/
theorem q7_independent_comp {ι κ : Type*} (v : ι → V) (f : κ → ι) (hf : Function.Injective f)
    (h : LinearIndependent K v) : LinearIndependent K (v ∘ f) := by
  sorry

/-- **Question 8.**

A finite family is linearly dependent if and only if one of its vectors lies in the span of all
the others.

Prove without using `linearIndependent_iff_notMem_span`. -/
theorem q8_dependent_mem_span {n : ℕ} (v : Fin (n + 1) → V) :
    ¬ LinearIndependent K v ↔ ∃ i, v i ∈ Submodule.span K (v '' {j | j ≠ i}) := by
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
