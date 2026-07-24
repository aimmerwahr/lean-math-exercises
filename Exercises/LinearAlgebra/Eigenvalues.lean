import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exercises — LinearAlgebra / Eigenvalues

An **eigenvector** of an operator `f : V → V` is a nonzero `v` with `f v = λ v`; the scalar `λ`
is the **eigenvalue**. Rewriting `f v = λ v` as `(f - λ·id) v = 0` shows the λ-eigenvectors are
exactly the nonzero elements of `ker (f - λ·id)`, so `λ` is an eigenvalue precisely when
`f - λ·id` fails to be injective. A clean structural fact — provable *without* determinants — is
that **eigenvectors for distinct eigenvalues are linearly independent**. Whether eigenvalues
exist at all depends on the field: a rotation of `ℝ²` has none over `ℝ` but does over `ℂ`.

Here `Module.End K V` is the type of operators `V →ₗ[K] V`, and `Matrix.toLin' A` is the map
`v ↦ A · v`.

Prove each statement yourself; the canonical proofs live in
`Solutions/LinearAlgebra/Eigenvalues.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma; those bans are enforced when
you build the project.
-/

namespace Exercises.LinearAlgebra.Eigenvalues

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Membership in a kernel; injectivity as trivial kernel; a nonzero element of a nonzero subspace.
#check @LinearMap.mem_ker
#check @LinearMap.ker_eq_bot
#check @Submodule.ne_bot_iff

-- A vanishing combination of a pair; `c • v = 0 ↔ c = 0 ∨ v = 0`.
#check @LinearIndependent.pair_iff
#check @smul_eq_zero

end

/-- **Question 1.**

A vector is a `λ`-eigenvector exactly when it lies in the kernel of `f - λ·id`:
`f v = λ • v ↔ v ∈ ker (f - λ • 1)`.

Prove without using `Module.End.mem_eigenspace_iff`. -/
theorem q1_eigen_iff_ker (f : Module.End K V) (l : K) (v : V) :
    f v = l • v ↔ v ∈ LinearMap.ker (f - l • 1) := by
  sorry

/-- **Question 2.**

`λ` is an eigenvalue of `f` exactly when `f - λ·id` fails to be injective:
`(∃ v ≠ 0, f v = λ • v) ↔ ¬ Injective (f - λ • 1)`. -/
theorem q2_eigenvalue_iff_not_injective (f : Module.End K V) (l : K) :
    (∃ v : V, v ≠ 0 ∧ f v = l • v) ↔ ¬ Function.Injective ⇑(f - l • 1) := by
  sorry

/-- **Question 3.**

Eigenvectors for distinct eigenvalues are linearly independent: if `f v₁ = λ₁ v₁` and
`f v₂ = λ₂ v₂` with `v₁, v₂` nonzero and `λ₁ ≠ λ₂`, then `v₁, v₂` are linearly independent.

Prove without using `Module.End.eigenvectors_linearIndependent`. -/
theorem q3_distinct_independent (f : Module.End K V) (l₁ l₂ : K) (v₁ v₂ : V)
    (h₁ : f v₁ = l₁ • v₁) (h₂ : f v₂ = l₂ • v₂)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hl : l₁ ≠ l₂) :
    LinearIndependent K ![v₁, v₂] := by
  sorry

/-- **Question 4.**

The matrix `!![2,1;1,2]` has eigenvalue `3` with eigenvector `(1,1)` and eigenvalue `1` with
eigenvector `(1,-1)`. -/
theorem q4_eig_2x2 :
    Matrix.toLin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] = (3 : ℝ) • ![1, 1] ∧
    Matrix.toLin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) ![1, -1] = (1 : ℝ) • ![1, -1] := by
  sorry

/-- **Question 5.**

Field dependence: the `90°` rotation `!![0,-1;1,0]` has **no** eigenvalue over `ℝ`, yet over `ℂ`
the vector `(i, 1)` is an eigenvector with eigenvalue `i`. -/
theorem q5_rotation_field_dependence :
    (¬ ∃ (μ : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧
      Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) v = μ • v) ∧
    Matrix.toLin' (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ![Complex.I, 1]
      = Complex.I • ![Complex.I, 1] := by
  sorry

/-- **Question 6.**

The shear `!![1,1;0,1]` has `1` as an eigenvalue, and its eigenvectors are exactly the vectors on
the `x`-axis: `toLin' A v = v ↔ v 1 = 0`. (So the eigenspace is the one-dimensional line
`span{(1,0)}`.) -/
theorem q6_shear_eigenspace (v : Fin 2 → ℝ) :
    Matrix.toLin' (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) v = v ↔ v 1 = 0 := by
  sorry

/-- **Question 7.**

The eigenvalues of a diagonal matrix are its diagonal entries: for `!![2,0;0,3]`, the standard
basis vectors are eigenvectors with eigenvalues `2` and `3`. -/
theorem q7_diagonal_eigs :
    Matrix.toLin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] = (2 : ℝ) • ![1, 0] ∧
    Matrix.toLin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = (3 : ℝ) • ![0, 1] := by
  sorry

/-- **Question 8.**

The two eigenvectors of `!![2,1;1,2]` found above are linearly independent. -/
theorem q8_distinct_independent_concrete :
    LinearIndependent ℝ ![(![1, 1] : Fin 2 → ℝ), ![1, -1]] := by
  sorry

end Exercises.LinearAlgebra.Eigenvalues
