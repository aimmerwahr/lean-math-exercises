import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Matrices

Once bases are fixed, **linear maps and matrices are the same thing**: a matrix acts on vectors
by `v ↦ A · v`, and this dictionary turns composition of maps into matrix multiplication and
identity into the identity matrix. A square matrix is invertible exactly when its map is a
bijection, and — a striking consequence of the finite-dimensional rigidity `injective ↔
surjective` — a one-sided inverse of a square matrix is automatically two-sided. This sheet is
where the abstract theory becomes computational.

Here `Matrix.toLin' A` is the linear map `v ↦ A · v` (standard basis), and `!![…]` is explicit
matrix notation.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/06Matrices.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project.
-/

namespace Exercises.LinearAlgebra.Matrices

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- The map of a matrix, and how matrix action composes: `(A * B) · v = A · (B · v)`.
#check @Matrix.toLin'_apply
#check @Matrix.mulVec_mulVec
#check @Matrix.toLin'_one

-- `toLin'` is injective, and the finite-dimensional rigidity behind the one-sided inverse.
#check @Matrix.toLin'
#check @LinearMap.injective_iff_surjective
#check @Function.LeftInverse.rightInverse_of_surjective

-- Expanding `2×2` products and the identity, for the concrete computations.
#check @Matrix.mul_fin_two
#check @Matrix.one_fin_two

-- The trace, and its cyclic property `tr (A B) = tr (B A)`.
#check @Matrix.trace_mul_comm
#check @Matrix.trace_sub
#check @Matrix.trace_one

end

/-- **Question 1.**

Compute the product of the `2 × 2` matrices
`[[1, 2], [3, 4]]` and `[[5, 6], [7, 8]]`. -/
theorem q1_matmul_concrete :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) * !![5, 6; 7, 8] = !![19, 22; 43, 50] := by
  sorry


/-- **Question 2.**

Matrix multiplication is not commutative: for `A = !![1,1;0,1]` and `B = !![1,0;1,1]`,
`A * B ≠ B * A`. -/
theorem q2_noncommute :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 1, 1]
      ≠ !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
  sorry


/-- **Question 3.**

The matrix `!![0,-1;1,0]` acts as the `90°` rotation of `ℝ²`: it sends `(1,0)` to `(0,1)` and
`(0,1)` to `(-1,0)`. -/
theorem q3_rotation_action :
    Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] = ![0, 1] ∧
    Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = ![-1, 0] := by
  sorry


/-- **Question 4.**

Composition of the associated maps corresponds to matrix multiplication:
`toLin' (A * B) = toLin' A ∘ toLin' B`.

Prove without using `Matrix.toLin'_mul`. -/
theorem q4_comp_eq_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.toLin' (A * B) = (Matrix.toLin' A).comp (Matrix.toLin' B) := by
  sorry


/-- **Question 5.**

For square matrices, a one-sided inverse is automatically two-sided: if `A * B = 1`, then
`B * A = 1`. (Pass to the associated maps and use `injective ↔ surjective` in finite dimension)

Prove without using `Matrix.mul_eq_one_comm`. -/
theorem q5_one_sided_inverse (A B : Matrix (Fin 2) (Fin 2) ℝ) (hAB : A * B = 1) : B * A = 1 := by
  sorry


/-- **Question 6.**

Verify that `!![2,1;1,1]` is invertible with inverse `!![1,-1;-1,2]`, by checking their product
is the identity. -/
theorem q6_inverse_concrete :
    (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, -1; -1, 2] = 1 := by
  sorry


/-- **Question 7.**

The **trace** of a square matrix is the sum of its diagonal entries. For a `2 × 2` matrix `A`,
show that `tr A = A₁₁ + A₂₂`. -/
theorem q7_trace_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace A = A 0 0 + A 1 1 := by
  sorry


/-- **Question 8.**

This begins a trace mini-sequence. Define a candidate trace on endomorphisms of `ℝ²` from its action
on the standard basis; do not invoke Mathlib's packaged trace. The candidate should be a linear
functional, vanish on commutators, and take the value `2` on the identity.

The follow-up characterization uses matrix units: a cyclic linear functional kills off-diagonal
units and takes the same value on every diagonal unit, hence is a multiple of trace; its value on
the identity fixes that multiple. -/
theorem q8_trace_unique (f : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (h : ∀ A, f A = A 0 0 + A 1 1) : f = Matrix.trace := by
  sorry


/-- **Question 9.**

There are no real matrices `A, B` with `A B − B A = I`.

Hint: apply trace to the proposed equation. -/
theorem q9_no_commutator_eq_one (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B - B * A ≠ 1 := by
  sorry


/-- **Question 10.**

Show that trace is a *similarity invariant*: if `Q P = I`, then `tr (P A Q) = tr A`, so `A` and
its representation `P A Q` in another basis have the same trace. -/
theorem q10_trace_conj_invariant (A P Q : Matrix (Fin 2) (Fin 2) ℝ) (h : Q * P = 1) :
    Matrix.trace (P * A * Q) = Matrix.trace A := by
  sorry


end Exercises.LinearAlgebra.Matrices
