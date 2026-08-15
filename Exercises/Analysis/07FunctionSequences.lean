import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Exercises — Analysis / FunctionSequences

A sequence of functions can converge at each individual input without doing so at a common rate.
Uniform convergence is the extra control that permits global conclusions, notably preservation of
continuity.  The examples below compare the two notions through powers, geometric partial sums,
and smooth approximations to an absolute value.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/07FunctionSequences.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular theorem. These bans are enforced
automatically when you build the project: if a proof uses a banned theorem (directly or through
automation), the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.Analysis.FunctionSequences

open Filter Set

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- The epsilon--`N` form of convergence of a scalar sequence.
#check @Metric.tendsto_atTop
#check @tendsto_pow_atTop_nhds_zero_of_lt_one

-- Continuity at a point relative to a specified domain.
#check @Metric.continuousWithinAt_iff
#check @ContinuousOn.continuousWithinAt

-- A finite geometric sum and the intermediate-value principle.
#check @geom_sum_mul
#check @intermediate_value_Icc

-- Square-root order facts and derivatives.
#check @Real.sqrt_lt'
#check @Real.sq_sqrt
#check @DifferentiableAt.sqrt

end

/-- `uₙ` converges uniformly to `f` on `s` when one index works for every point of `s`.
This explicit epsilon--`N` form is equivalent to Mathlib's `TendstoUniformlyOn` formulation, but
keeps the quantifiers visible in these exercises. -/
def UniformlyConvergesOn (u : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - f x| < ε

/-- The pointwise limit of the powers `x^(n+1)` on `[0,1]`. -/
noncomputable def powersLimit (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- The `n`th partial sum of the geometric series `∑ x^k`. -/
noncomputable def geometricPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ k

/-- A smooth positive approximation to `|x|`. -/
noncomputable def smoothAbs (n : ℕ) (x : ℝ) : ℝ :=
  √(x ^ 2 + 1 / ((n : ℝ) + 1))


/-- **Question 1.**

If `0 ≤ a < 1`, then `x ↦ x^n` converges uniformly to `0` on `[0,a]`.

Prove the uniform statement from the bound `0 ≤ x^n ≤ a^n`. -/
theorem q1_powers_uniform_on_smaller_interval {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    UniformlyConvergesOn (fun n x => x ^ n) (fun _ => 0) (Icc 0 a) := by
  sorry


/-- **Question 2.**

On `[0,1]`, the functions `x ↦ x^(n+1)` converge pointwise to `powersLimit`: the value is `0`
below `1` and `1` at the endpoint. -/
theorem q2_powers_pointwise :
    ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => x ^ (n + 1)) atTop (nhds (powersLimit x)) := by
  sorry


/-- **Question 3.**

The pointwise convergence in Question 2 is not uniform on `[0,1]`.

Use the explicit epsilon--`N` definition of `UniformlyConvergesOn`. -/
theorem q3_powers_not_uniform :
    ¬ UniformlyConvergesOn (fun n x => x ^ (n + 1)) powersLimit (Icc 0 1) := by
  sorry


/-- **Question 4.**

If every `u n` is continuous on `K` and `u` converges uniformly to `f` there, then `f` is
continuous on `K`.

At a point `x ∈ K`, unfold `huf : UniformlyConvergesOn u f K` with a small positive error to
obtain one index `N` that controls `|u N z - f z|` for every `z ∈ K`. Apply the continuity of
`u N` at `x` to control `|u N y - u N x|` for nearby `y ∈ K`, then combine these estimates to
control `|f y - f x|`. -/
theorem q4_uniform_limit_continuous_on {K : Set ℝ} {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hu : ∀ n, ContinuousOn (u n) K) (huf : UniformlyConvergesOn u f K) :
    ContinuousOn f K := by
  sorry


/-- **Question 5.**

If `0 ≤ a < 1`, then the geometric partial sums converge uniformly on `[-a,a]` to
`x ↦ (1-x)⁻¹`.

First derive an explicit tail bound. -/
theorem q5_geometric_function_series {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    UniformlyConvergesOn geometricPartialSum (fun x => 1 / (1 - x)) (Icc (-a) a) := by
  sorry


/-- **Question 6.**

The geometric-series sum `x ↦ (1-x)⁻¹` is continuous on `[-a,a]` for every `0 ≤ a < 1`, by
viewing it as the uniform limit from Question 5.

Prove without a direct continuity theorem for inverse or division. -/
theorem q6_geometric_series_continuous {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    ContinuousOn (fun x => 1 / (1 - x)) (Icc (-a) a) := by
  sorry


/-- **Question 7.**

Each `smoothAbs n` is differentiable on `ℝ`, and these functions converge uniformly to `|x|`.

Prove the uniform square-root estimate and the differentiability of every approximant. -/
theorem q7_smooth_approximation_uniform :
    UniformlyConvergesOn smoothAbs (abs : ℝ → ℝ) (univ : Set ℝ) ∧
      ∀ n, Differentiable ℝ (smoothAbs n) := by
  sorry


/-- **Question 8.**

The uniform limit in Question 7, `|x|`, is not differentiable at `0`.

Prove this by comparing its one-sided derivatives, without using
`not_differentiableAt_abs_zero`. -/
theorem q8_abs_not_differentiable_at_zero :
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) (0 : ℝ) := by
  sorry

end Exercises.Analysis.FunctionSequences
