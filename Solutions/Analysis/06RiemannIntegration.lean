import Solutions.Analysis.«05Differentiation»
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace Solutions.Analysis.RiemannIntegration

open MeasureTheory Set
open scoped Interval


theorem q1_integral_triangle_inequality {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  -- Pointwise, `f` lies between its negative absolute value and its absolute value.
  have habs : IntervalIntegrable (fun x => |f x|) volume a b := hfi.norm
  have hlower := intervalIntegral.integral_mono_on hab habs.neg hfi fun x _ => neg_abs_le (f x)
  have hupper := intervalIntegral.integral_mono_on hab hfi habs fun x _ => le_abs_self (f x)
  have hlower' : -(∫ x in a..b, |f x|) ≤ ∫ x in a..b, f x := by
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using hlower
  exact abs_le.2 ⟨by linarith, hupper⟩


theorem q2_integral_affine (a b m c : ℝ) :
    ∫ x in a..b, (m * x + c) = (m / 2) * (b ^ 2 - a ^ 2) + c * (b - a) := by
  -- The proposed antiderivative has derivative `x ↦ m*x + c`.
  let F : ℝ → ℝ := fun x => (m / 2) * x ^ 2 + c * x
  have hderiv : deriv F = fun x : ℝ => m * x + c := by
    funext x
    change deriv ((fun y : ℝ => (m / 2) * y ^ 2) + fun y => c * y) x = _
    have h := (((hasDerivAt_id x).pow 2).const_mul (m / 2)).add
      ((hasDerivAt_id x).const_mul c)
    have h' : deriv ((fun y : ℝ => (m / 2) * y ^ 2) + fun y => c * y) x =
        (m / 2) * (2 * x) + c := by
      simpa [id, Nat.reduceSub] using h.deriv
    calc
      deriv ((fun y : ℝ => (m / 2) * y ^ 2) + fun y => c * y) x = (m / 2) * (2 * x) + c := h'
      _ = m * x + c := by ring
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ F x := by
    intro x _
    dsimp [F]
    fun_prop
  have hcont : ContinuousOn (fun x : ℝ => m * x + c) (uIcc a b) := by
    fun_prop
  have hFTC : (∫ x in a..b, (m * x + c)) = F b - F a :=
    intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
  calc
    ∫ x in a..b, (m * x + c) = F b - F a := hFTC
    _ = (m / 2) * (b ^ 2 - a ^ 2) + c * (b - a) := by
      dsimp [F]
      ring


theorem q3_integration_by_parts {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x : ℝ, HasDerivAt u (u' x) x) (hv : ∀ x : ℝ, HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  -- The derivative of the product records both ways that the product can change.
  have hucont : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hvcont : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
  have hleft : IntervalIntegrable (fun x => u' x * v x) volume a b := by
    simpa [mul_comm] using hu'.continuousOn_mul hvcont.continuousOn
  have hright : IntervalIntegrable (fun x => u x * v' x) volume a b :=
    hv'.continuousOn_mul hucont.continuousOn
  have hproduct : ∀ x : ℝ, deriv (u * v) x = u' x * v x + u x * v' x := by
    intro x
    rw [deriv_mul (hu x).differentiableAt (hv x).differentiableAt, (hu x).deriv, (hv x).deriv]
  have hdiffproduct : ∀ x ∈ uIcc a b, DifferentiableAt ℝ (u * v) x := by
    intro x _
    exact (hu x).differentiableAt.mul (hv x).differentiableAt
  have hderivint : IntervalIntegrable (deriv (u * v)) volume a b := by
    convert hleft.add hright using 1
    funext x
    exact hproduct x
  have hendpoint := intervalIntegral.integral_deriv_eq_sub hdiffproduct hderivint
  have hsum : (∫ x in a..b, deriv (u * v) x) =
      (∫ x in a..b, u' x * v x) + ∫ x in a..b, u x * v' x := by
    calc
      ∫ x in a..b, deriv (u * v) x = ∫ x in a..b, (u' x * v x + u x * v' x) := by
        congr 1
        funext x
        exact hproduct x
      _ = (∫ x in a..b, u' x * v x) + ∫ x in a..b, u x * v' x :=
        intervalIntegral.integral_add hleft hright
  rw [hsum] at hendpoint
  simp only [Pi.mul_apply] at hendpoint
  linarith


theorem q4_integral_x_exp :
    ∫ x in (0 : ℝ)..1, x * Real.exp x = 1 := by
  -- Move the derivative from the exponential to the identity function.
  have hparts := q3_integration_by_parts (a := (0 : ℝ)) (b := 1)
    (u := id) (v := Real.exp) (u' := fun _ => 1) (v' := Real.exp)
    (fun x => hasDerivAt_id x) (fun x => Real.hasDerivAt_exp x)
    (continuous_const.intervalIntegrable 0 1) (Real.continuous_exp.intervalIntegrable 0 1)
  -- The remaining exponential integral is its endpoint difference.
  have hexp : (∫ x in (0 : ℝ)..1, Real.exp x) = Real.exp 1 - Real.exp 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_exp x) (Real.continuous_exp.intervalIntegrable 0 1)
  simp only [id_eq, one_mul, zero_mul, Real.exp_zero] at hparts
  rw [hexp] at hparts
  rw [Real.exp_zero] at hparts
  linarith


theorem q5_continuous_nonneg_integral_eq_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hint : ∫ x in a..b, f x = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  intro x hx
  apply le_antisymm ?_ (hnonneg x hx)
  by_contra hzero
  have hpos : 0 < f x := lt_of_not_ge hzero
  -- A continuous nonnegative function that is positive somewhere has strictly positive area.
  have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    continuousOn_const hcont (fun y hy => hnonneg y ⟨hy.1.le, hy.2⟩) ⟨x, hx, hpos⟩
  norm_num [intervalIntegral.integral_const, hint] at hstrict


theorem q6_integral_sq_eq_zero_iff {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x ^ 2 = 0) ↔ ∀ x ∈ Icc a b, f x = 0 := by
  constructor
  · intro hint
    have hsquares := q5_continuous_nonneg_integral_eq_zero (f := f ^ 2) hab (hcont.pow 2)
      (fun x _ => sq_nonneg (f x)) hint
    intro x hx
    simpa using hsquares x hx
  · intro hzero
    calc
      ∫ x in a..b, f x ^ 2 = ∫ _x in a..b, 0 := intervalIntegral.integral_congr (by
        intro x hx
        have hx' : x ∈ Icc a b := by simpa [uIcc_of_le hab.le] using hx
        simp [hzero x hx'])
      _ = 0 := by simp


theorem q7_abs_integral_le_bound {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ M) :
    |∫ x in a..b, f x| ≤ M * (b - a) := by
  have habs : IntervalIntegrable (fun x => |f x|) volume a b := hfi.norm
  have hconst : IntervalIntegrable (fun _ : ℝ => M) volume a b := continuous_const.intervalIntegrable _ _
  have hbound_int := intervalIntegral.integral_mono_on hab habs hconst hbound
  calc
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := q1_integral_triangle_inequality hab hfi
    _ ≤ ∫ _x in a..b, M := hbound_int
    _ = M * (b - a) := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]; ring


theorem q8_weighted_integral_bounds {f g : ℝ → ℝ} {a b m M : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg_nonneg : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hlower : ∀ x ∈ Icc a b, m ≤ f x) (hupper : ∀ x ∈ Icc a b, f x ≤ M) :
    m * (∫ x in a..b, g x) ≤ ∫ x in a..b, f x * g x ∧
      (∫ x in a..b, f x * g x) ≤ M * ∫ x in a..b, g x := by
  have hf_u : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab.le] using hf
  have hg_u : ContinuousOn g (uIcc a b) := by simpa [uIcc_of_le hab.le] using hg
  have hgint : IntervalIntegrable g volume a b := hg_u.intervalIntegrable
  -- A continuous factor times an integrable weight is still integrable.
  have hfgint : IntervalIntegrable (fun x => f x * g x) volume a b :=
    hgint.continuousOn_smul hf_u
  have hmint : IntervalIntegrable (fun x => m * g x) volume a b := by
    simpa only [smul_eq_mul] using
      (hgint.continuousOn_smul
        (continuousOn_const : ContinuousOn (fun _ : ℝ => m) (uIcc a b)))
  have hMint : IntervalIntegrable (fun x => M * g x) volume a b := by
    simpa only [smul_eq_mul] using
      (hgint.continuousOn_smul
        (continuousOn_const : ContinuousOn (fun _ : ℝ => M) (uIcc a b)))
  constructor
  · -- The lower pointwise bound remains a lower bound after weighting and integrating.
    simpa only [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_mono_on hab.le hmint hfgint fun x hx =>
        mul_le_mul_of_nonneg_right (hlower x hx) (hg_nonneg x hx))
  · -- The same argument applies to the upper pointwise bound.
    simpa only [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_mono_on hab.le hfgint hMint fun x hx =>
        mul_le_mul_of_nonneg_right (hupper x hx) (hg_nonneg x hx))


theorem q9_weighted_integral_mean_value {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg_nonneg : ∀ x ∈ Icc a b, 0 ≤ g x) :
    ∃ c ∈ Icc a b, (∫ x in a..b, f x * g x) = f c * ∫ x in a..b, g x := by
  -- The extrema of `f` give the pointwise bounds required by Question 8.
  have hcompact : IsCompact (Icc a b) := isCompact_Icc
  have hnonempty : (Icc a b).Nonempty := nonempty_Icc.mpr hab.le
  obtain ⟨p, hp, hpmin⟩ := hcompact.exists_isMinOn hnonempty hf
  obtain ⟨q, hq, hqmax⟩ := hcompact.exists_isMaxOn hnonempty hf
  obtain ⟨hlower, hupper⟩ := q8_weighted_integral_bounds (m := f p) (M := f q)
    hab hf hg hg_nonneg (fun x hx => hpmin hx) (fun x hx => hqmax hx)
  have hI_nonneg : 0 ≤ ∫ x in a..b, g x := intervalIntegral.integral_nonneg hab.le hg_nonneg
  by_cases hIzero : ∫ x in a..b, g x = 0
  · -- When the total weight is zero, the two bounds force the weighted integral to be zero.
    have hproduct_zero : (∫ x in a..b, f x * g x) = 0 := le_antisymm
      (by simpa [hIzero] using hupper) (by simpa [hIzero] using hlower)
    exact ⟨a, ⟨le_rfl, hab.le⟩, by rw [hproduct_zero, hIzero]; ring⟩
  · have hIpos : 0 < ∫ x in a..b, g x := lt_of_le_of_ne hI_nonneg (Ne.symm hIzero)
    -- Dividing the two bounds by the positive total weight puts the weighted average
    -- between two values attained by `f`.
    have hlow : f p ≤ (∫ x in a..b, f x * g x) / (∫ x in a..b, g x) :=
      (le_div_iff₀ hIpos).2 hlower
    have hupp : (∫ x in a..b, f x * g x) / (∫ x in a..b, g x) ≤ f q :=
      (div_le_iff₀ hIpos).2 hupper
    obtain ⟨c, hc, hfc⟩ := (isPreconnected_Icc.intermediate_value hp hq hf) ⟨hlow, hupp⟩
    refine ⟨c, hc, ?_⟩
    -- The defining equality for this attained average is exactly the required identity.
    rw [hfc]
    field_simp


end Solutions.Analysis.RiemannIntegration
