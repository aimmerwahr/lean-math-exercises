import Exercises.Analysis.«05Differentiation»
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Exercises — Analysis / Elementary Functions

The real exponential, logarithm, sine, and cosine form a small collection of functions whose
algebraic identities, continuity, and derivatives illuminate general ideas throughout analysis.
Derivative information gives global inequalities through the mean-value theorem; inverse
relations transport estimates between exponential and logarithmic functions; and continuity
turns sign changes into existence statements. These functions therefore provide a testing ground
where local calculus yields useful global conclusions.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/08ElementaryFunctions.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular theorem. These bans are enforced
automatically when you build the project: if a proof uses a banned theorem (directly or through
automation), the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.Analysis.ElementaryFunctions

open Set

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Derivatives and endpoint values of the elementary functions.
#check @Real.hasDerivAt_exp
#check @Real.hasDerivAt_cos
#check @Real.exp_log
#check @Real.continuousOn_log
#check @Real.differentiableOn_log

-- Comparing values through the mean-value theorem.
#check @exists_deriv_eq_slope
#check @Real.exp_le_exp
#check @Real.exp_lt_exp
#check @Real.abs_cos_le_one
#check @Real.log_le_log

-- Passing from a pointwise estimate to a finite product.
#check @Real.exp_nat_mul
#check @pow_le_pow_left₀

-- Trigonometric identities and continuity-based existence.
#check @Real.sin_sq_add_cos_sq
#check @Real.cos_neg
#check @intermediate_value_Icc

end


/-- **Question 1.**

For every real `x`, prove `1 + x ≤ exp x`.

Prove without using `Real.add_one_le_exp`. -/
theorem q1_exp_tangent_bound (x : ℝ) :
    1 + x ≤ Real.exp x := by
  sorry


/-- **Question 2.**

For every `x > 0`, prove `log x ≤ x - 1`.

Question 1 supplies the exponential estimate used here.

Prove without using `Real.log_le_sub_one_of_pos`. -/
theorem q2_log_tangent_bound {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x - 1 := by
  sorry


/-- **Question 3.**

For every real `x`, prove `|sin x| ≤ |x|`.

Prove without using `Real.abs_sin_le_abs`, `Real.abs_sin_sub_sin_le`, or
`Real.lipschitzWith_sin`. -/
theorem q3_sin_lipschitz (x : ℝ) :
    |Real.sin x| ≤ |x| := by
  sorry


/-- **Question 4.**

For every real `x`, prove `1 - x²/2 ≤ cos x ≤ 1`.

Question 3 supplies the sine estimate used for the lower bound.

Prove without using `Real.one_sub_sq_div_two_le_cos` or `Real.cos_le_one`. -/
theorem q4_cos_quadratic_bound (x : ℝ) :
    1 - x ^ 2 / 2 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
  sorry


/-- **Question 5.**

For positive real `x` and `y`, prove
`|log x - log y| ≤ |x - y| / min x y`. -/
theorem q5_log_difference_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ |x - y| / min x y := by
  sorry


/-- **Question 6.**

For every positive integer `n`, prove
`(1 + 1/n)^n ≤ exp 1`.

Question 1 supplies the estimate that is applied to each factor. -/
theorem q6_binomial_approx_le_exp (n : ℕ) (hn : 0 < n) :
    (1 + (n : ℝ)⁻¹) ^ n ≤ Real.exp 1 := by
  sorry


/-- **Question 7.**

Let `F(x) = x - exp (-x)`. Prove that `F` is strictly increasing on the real line. -/
theorem q7_exp_neg_difference_strict_mono :
    StrictMono (fun x : ℝ => x - Real.exp (-x)) := by
  sorry


/-- **Question 8.**

There is a unique `x ∈ (0,1)` such that `exp (-x) = x`.

Question 7 supplies the uniqueness argument; establish the existence of the zero. -/
theorem q8_exp_neg_fixed_point :
    ∃! x : ℝ, x ∈ Ioo 0 1 ∧ Real.exp (-x) = x := by
  sorry

end Exercises.Analysis.ElementaryFunctions
