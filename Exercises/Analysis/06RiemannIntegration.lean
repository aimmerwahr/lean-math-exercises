import Exercises.Analysis.«05Differentiation»
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Exercises — Analysis / Riemann Integration

Riemann integration records accumulated change by approximating an area with finite sums over
finer and finer partitions. Continuous functions on a closed interval are integrable, and the
integral respects linearity and order. The fundamental theorem of calculus then links integration
to differentiation: an accumulated derivative is the difference of endpoint values. These ideas
give both concrete evaluations and structural information, such as when a nonnegative function
must vanish or when a weighted average is attained.

## Lean notation

Lean writes the usual definite integral `∫ₐᵇ f(x) dx` as `∫ x in a..b, f x`.  Here `x` is the
bound variable, `a..b` gives the lower and upper endpoints, and `f x` is the integrand; the
two dots are Lean's interval-integral notation, not an ellipsis.  Thus
`|∫ x in a..b, f x|` means the absolute value of the definite integral.  The order of the
endpoints matters: reversing them negates the integral, just as in the usual convention.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/06RiemannIntegration.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular theorem. These bans are enforced
automatically when you build the project: if a proof uses a banned theorem (directly or through
automation), the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.Analysis.RiemannIntegration

open MeasureTheory Set
open scoped Interval

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Comparing integrals and simplifying the integral of a constant.
#check @intervalIntegral.integral_mono_on
#check @intervalIntegral.integral_add
#check @intervalIntegral.integral_neg
#check @intervalIntegral.integral_const
#check @intervalIntegral.integral_const_mul
#check @intervalIntegral.integral_congr

-- Producing interval integrability from continuity.
#check @Continuous.intervalIntegrable
#check @ContinuousOn.intervalIntegrable
#check @IntervalIntegrable.norm
#check @IntervalIntegrable.continuousOn_mul

-- Fundamental-theorem and derivative tools.
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt
#check @intervalIntegral.integral_deriv_eq_sub
#check @intervalIntegral.integral_deriv_eq_sub'
#check @deriv_mul
#check @HasDerivAt.add
#check @HasDerivAt.mul
#check @HasDerivAt.pow

-- Extrema and intermediate values on a closed interval.
#check @isCompact_Icc
#check @IsCompact.exists_isMinOn
#check @IsCompact.exists_isMaxOn
#check @intermediate_value_Icc

end


/-- **Question 1.**

Let `a ≤ b`, and let `f` be interval integrable on `[a,b]`. Prove
`|∫ x in a..b, f x| ≤ ∫ x in a..b, |f x|`.

Prove without using `intervalIntegral.norm_integral_le_integral_norm`. -/
theorem q1_integral_triangle_inequality {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  sorry


/-- **Question 2.**

For real `a`, `b`, `m`, and `c`, evaluate
`∫ x in a..b, (m*x+c) = (m/2)(b²-a²) + c(b-a)`.
-/
theorem q2_integral_affine (a b m c : ℝ) :
    ∫ x in a..b, (m * x + c) = (m / 2) * (b ^ 2 - a ^ 2) + c * (b - a) := by
  sorry


/-- **Question 3.**

Let `u` and `v` have derivatives `u'` and `v'`, respectively, and suppose those derivatives are
interval integrable on `[a,b]`. Prove
`∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x`.

Prove without using `intervalIntegral.integral_mul_deriv_eq_deriv_mul` or
`intervalIntegral.integral_deriv_mul_eq_sub`. -/
theorem q3_integration_by_parts {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x : ℝ, HasDerivAt u (u' x) x) (hv : ∀ x : ℝ, HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  sorry


/-- **Question 4.**

Use Question 3 to evaluate `∫ x in 0..1, x * exp x = 1`.

Question 3 supplies the integration-by-parts identity. -/
theorem q4_integral_x_exp :
    ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  sorry


/-- **Question 5.**

Let `a < b`, and let `f` be continuous and nonnegative on `[a,b]`. If
`∫ x in a..b, f x = 0`, then `f x = 0` for every `x ∈ [a,b]`.

Prove without using `intervalIntegral.integral_eq_zero_iff_of_nonneg_ae` or
`intervalIntegral.integral_pos`. -/
theorem q5_continuous_nonneg_integral_eq_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hint : ∫ x in a..b, f x = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  sorry


/-- **Question 6.**

Let `a < b` and let `f` be continuous on `[a,b]`. Prove that
`∫ x in a..b, f x² = 0` if and only if `f` vanishes at every point of `[a,b]`.

Question 5 supplies the implication from a zero integral to pointwise vanishing. -/
theorem q6_integral_sq_eq_zero_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x ^ 2 = 0) ↔ ∀ x ∈ Icc a b, f x = 0 := by
  sorry


/-- **Question 7.**

Let `a ≤ b`, let `f` be interval integrable on `[a,b]`, and suppose `|f x| ≤ M` on `[a,b]`.
Prove `|∫ x in a..b, f x| ≤ M*(b-a)`.

Prove without using `intervalIntegral.norm_integral_le_of_norm_le`. -/
theorem q7_abs_integral_le_bound {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ M) :
    |∫ x in a..b, f x| ≤ M * (b - a) := by
  sorry


/-- **Question 8.**

Let `a < b`, let `f` and `g` be continuous on `[a,b]`, and suppose `g` is nonnegative there.
If `m ≤ f x ≤ M` for every `x ∈ [a,b]`, prove
`m * ∫ x in a..b, g x ≤ ∫ x in a..b, f x * g x ≤ M * ∫ x in a..b, g x`.
-/
theorem q8_weighted_integral_bounds {f g : ℝ → ℝ} {a b m M : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg_nonneg : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hlower : ∀ x ∈ Icc a b, m ≤ f x) (hupper : ∀ x ∈ Icc a b, f x ≤ M) :
    m * (∫ x in a..b, g x) ≤ ∫ x in a..b, f x * g x ∧
      (∫ x in a..b, f x * g x) ≤ M * ∫ x in a..b, g x := by
  sorry


/-- **Question 9.**

Let `a < b`, let `f` and `g` be continuous on `[a,b]`, and suppose `g` is nonnegative there.
Prove that some `c ∈ [a,b]` satisfies
`∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x`.

Question 8 supplies the integral bounds used here.

Prove without using `exists_eq_const_mul_intervalIntegral_of_ae_nonneg` or
`exists_eq_const_mul_intervalIntegral_of_nonneg`. -/
theorem q9_weighted_integral_mean_value {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg_nonneg : ∀ x ∈ Icc a b, 0 ≤ g x) :
    ∃ c ∈ Icc a b, (∫ x in a..b, f x * g x) = f c * ∫ x in a..b, g x := by
  sorry

end Exercises.Analysis.RiemannIntegration
