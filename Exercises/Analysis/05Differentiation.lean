import Exercises.Analysis.«04ContinuousFunctions»
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Exercises — Analysis / Differentiation

Differentiability says that, at a sufficiently small scale, a function is well approximated by a
linear map. For real functions that linear map is multiplication by the derivative. The algebra of
derivatives makes local computations possible; the mean-value theorem makes local slope control
global change. A bound on derivatives can therefore prove monotonicity, comparison estimates, and
even the existence of a unique fixed point.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/05Differentiation.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular theorem. These bans are enforced
automatically when you build the project: if a proof uses a banned theorem (directly or through
automation), the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.Analysis.Differentiation

open Filter Set
open Exercises.Analysis.ContinuousFunctions

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Building derivatives from elementary functions.
#check hasDerivAt_id
#check HasDerivAt.add
#check HasDerivAt.sub
#check HasDerivAt.mul
#check HasDerivAt.pow
#check Real.hasDerivAt_exp
#check Real.hasDerivAt_sin
#check Real.hasDerivAt_cos

-- Turning a derivative estimate into a statement about an interval.
#check exists_deriv_eq_slope
#check Differentiable.continuous
#check Differentiable.differentiableOn
#check Continuous.continuousOn

-- Packaging a contraction and using its fixed point.
#check LipschitzWith.of_dist_le_mul
#check ContractingWith.fixedPoint_isFixedPt
#check ContractingWith.fixedPoint_unique
#check ContractingWith.tendsto_iterate_fixedPoint

-- The difference-quotient formulation of a derivative.
#check hasDerivAt_iff_tendsto_slope_zero
#check Metric.tendsto_nhds

end

/-- **Question 1.**

For every real `x`, prove `(x³ - 3x² + 2x)' = 3x² - 6x + 2`. -/
theorem q1_deriv_cubic (x : ℝ) :
    deriv (fun y : ℝ => y ^ 3 - 3 * y ^ 2 + 2 * y) x = 3 * x ^ 2 - 6 * x + 2 := by
  sorry


/-- **Question 2.**

For every real `x`, prove `(x exp x)' = (x+1) exp x`. -/
theorem q2_deriv_x_exp (x : ℝ) :
    deriv (fun y : ℝ => y * Real.exp y) x = (x + 1) * Real.exp x := by
  sorry


/-- **Question 3.**

For every real `x`, the derivative of `sin²x + cos²x` is zero.

Prove without using `Real.sin_sq_add_cos_sq`. -/
theorem q3_deriv_sin_square_plus_cos_square (x : ℝ) :
    deriv (fun y : ℝ => Real.sin y ^ 2 + Real.cos y ^ 2) x = 0 := by
  sorry


/-- **Question 4.**

Let `f` be continuous on `[a,b]`, differentiable on `(a,b)`, and have derivative zero throughout
`(a,b)`. Then `f` is constant on `[a,b]`.

Prove without using `constant_of_derivWithin_zero`. -/
theorem q4_zero_deriv_constant_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hzero : ∀ x ∈ Ioo a b, deriv f x = 0) :
    ∀ x ∈ Icc a b, f x = f a := by
  sorry


/-- **Question 5.**

Let `f,g : ℝ → ℝ` be differentiable, with `f(0)=g(0)` and `f'(x) ≤ g'(x)` for every `x`.
Then `f(x) ≤ g(x)` for every `x ≥ 0`.

Prove without using `image_sub_le_mul_sub_of_deriv_le`,
`Convex.image_sub_le_mul_sub_of_deriv_le`, `monotoneOn_of_deriv_nonneg`, or
`monotone_of_deriv_nonneg`. -/
theorem q5_deriv_comparison_on_ray {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hzero : f 0 = g 0)
    (hderiv : ∀ x : ℝ, deriv f x ≤ deriv g x) :
    ∀ x ≥ 0, f x ≤ g x := by
  sorry


/-- **Question 6.**

If `f(0)=0` and `1 ≤ f'(x) ≤ 2` for every `x`, then `x ≤ f(x) ≤ 2x` for every `x ≥ 0`.

Question 5 is the comparison principle needed to compare `f` with the two linear functions. -/
theorem q6_deriv_bounds_on_ray {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hzero : f 0 = 0)
    (hderiv : ∀ x : ℝ, 1 ≤ deriv f x ∧ deriv f x ≤ 2) :
    ∀ x ≥ 0, x ≤ f x ∧ f x ≤ 2 * x := by
  sorry


/-- **Question 7.**

Let `a < b < c`. If `f` is continuous on `[a,c]`, differentiable on `(a,c)`, and
`f(a)=f(b)=f(c)=0`, then there are `u∈(a,b)` and `v∈(b,c)` with `f'(u)=f'(v)=0`.

Prove without using `exists_deriv_eq_zero` or `exists_hasDerivAt_eq_zero`. -/
theorem q7_three_zeros_two_critical_points {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hcont : ContinuousOn f (Icc a c)) (hdiff : DifferentiableOn ℝ f (Ioo a c))
    (hfa : f a = 0) (hfb : f b = 0) (hfc : f c = 0) :
    ∃ u ∈ Ioo a b, deriv f u = 0 ∧ ∃ v ∈ Ioo b c, deriv f v = 0 := by
  sorry


/-- **Question 8.**

Let `f : ℝ → ℝ` be differentiable and suppose `0 ≤ q < 1` and `|f'(x)| ≤ q` for every `x`.
Then `f` is a contraction with constant `q`.

Prove without using `lipschitzWith_of_nnnorm_deriv_le`. -/
theorem q8_deriv_bound_is_contracting {f : ℝ → ℝ} {q : ℝ} (hf : Differentiable ℝ f)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : ∀ x : ℝ, |deriv f x| ≤ q) :
    ContractingWith q.toNNReal f := by
  sorry


/-- **Question 9.**

Under the hypotheses of Question 8, `f` has a unique fixed point `p`; from every starting value
`x`, the iterates `f^[n](x)` converge to `p`.

Question 8 supplies the contraction needed for the fixed-point theorem. -/
theorem q9_contracting_fixed_point_and_iterates {f : ℝ → ℝ} {q : ℝ} (hf : Differentiable ℝ f)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : ∀ x : ℝ, |deriv f x| ≤ q) :
    ∃ p : ℝ, f p = p ∧ (∀ y : ℝ, f y = y → y = p) ∧
      ∀ x : ℝ, Tendsto (fun n : ℕ => f^[n] x) atTop (nhds p) := by
  sorry


/-- **Question 10.**

The damped oscillation `dampedOscillation 2`, given by `x² sin(1/x)` away from `0` and by `0` at
the origin, is differentiable at `0` with derivative `0`. -/
theorem q10_differentiable_damped_oscillation : HasDerivAt (dampedOscillation 2) 0 0 := by
  sorry

end Exercises.Analysis.Differentiation
