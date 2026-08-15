import Solutions.Analysis.«04ContinuousFunctions»
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

namespace Solutions.Analysis.Differentiation

open Filter Set
open Solutions.Analysis.ContinuousFunctions


theorem q1_deriv_cubic (x : ℝ) :
    deriv (fun y : ℝ => y ^ 3 - 3 * y ^ 2 + 2 * y) x = 3 * x ^ 2 - 6 * x + 2 := by
  -- Assemble the polynomial derivative from the power and scalar-multiple rules.
  change deriv ((id ^ 3 - fun y : ℝ => 3 * (id ^ 2) y) + fun y : ℝ => 2 * id y) x = _
  have h := (((hasDerivAt_id x).pow 3).sub (((hasDerivAt_id x).pow 2).const_mul 3)).add
    ((hasDerivAt_id x).const_mul 2)
  convert h.deriv using 1
  simp [id]
  ring


theorem q2_deriv_x_exp (x : ℝ) :
    deriv (fun y : ℝ => y * Real.exp y) x = (x + 1) * Real.exp x := by
  -- The product rule combines the identity's slope with the exponential's own value.
  change deriv (id * Real.exp) x = _
  have h := (hasDerivAt_id x).mul (Real.hasDerivAt_exp x)
  convert h.deriv using 1
  simp only [id_eq]
  ring


theorem q3_deriv_sin_square_plus_cos_square (x : ℝ) :
    deriv (fun y : ℝ => Real.sin y ^ 2 + Real.cos y ^ 2) x = 0 := by
  -- The two product-rule contributions cancel, without first using the trigonometric identity.
  change deriv (Real.sin ^ 2 + Real.cos ^ 2) x = 0
  have h := ((Real.hasDerivAt_sin x).pow 2).add ((Real.hasDerivAt_cos x).pow 2)
  convert h.deriv using 1
  ring


theorem q4_zero_deriv_constant_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hzero : ∀ x ∈ Ioo a b, deriv f x = 0) :
    ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases hx with ⟨hax, hxb⟩
  rcases hax.eq_or_lt with rfl | hax
  · rfl
  -- Apply the mean-value theorem only on the smaller interval `[a,x]`.
  have hcont_ax : ContinuousOn f (Icc a x) := hcont.mono fun y hy =>
    ⟨hy.1, le_trans hy.2 hxb⟩
  have hdiff_ax : DifferentiableOn ℝ f (Ioo a x) := hdiff.mono fun y hy =>
    ⟨hy.1, lt_of_lt_of_le hy.2 hxb⟩
  obtain ⟨c, hc, hcslope⟩ := exists_deriv_eq_slope f hax hcont_ax hdiff_ax
  have hczero : deriv f c = 0 := hzero c ⟨hc.1, lt_of_lt_of_le hc.2 hxb⟩
  rw [hczero] at hcslope
  field_simp at hcslope
  linarith


theorem q5_deriv_comparison_on_ray {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hzero : f 0 = g 0)
    (hderiv : ∀ x : ℝ, deriv f x ≤ deriv g x) :
    ∀ x ≥ 0, f x ≤ g x := by
  intro x hx
  rcases hx.eq_or_lt with rfl | hx
  · exact hzero.le
  -- The slope of `f-g` between `0` and `x` is nonpositive.
  let h : ℝ → ℝ := f - g
  have hhcont : ContinuousOn h (Icc 0 x) := (hf.sub hg).continuous.continuousOn
  have hhdiff : DifferentiableOn ℝ h (Ioo 0 x) := (hf.sub hg).differentiableOn
  obtain ⟨c, hc, hcslope⟩ := exists_deriv_eq_slope h hx hhcont hhdiff
  have hcdiff : DifferentiableAt ℝ f c := hf c
  have hcgdif : DifferentiableAt ℝ g c := hg c
  have hderiv_h : deriv h c = deriv f c - deriv g c := deriv_sub hcdiff hcgdif
  have hnonpos : deriv h c ≤ 0 := by rw [hderiv_h]; linarith [hderiv c]
  have hslope_nonpos : (h x - h 0) / (x - 0) ≤ 0 := by simpa [hcslope] using hnonpos
  have hendpoints : h x - h 0 ≤ 0 := by
    have hmul := (div_le_iff₀ (sub_pos.mpr hx)).mp hslope_nonpos
    simpa using hmul
  dsimp [h] at hendpoints
  linarith


theorem q6_deriv_bounds_on_ray {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hzero : f 0 = 0)
    (hderiv : ∀ x : ℝ, 1 ≤ deriv f x ∧ deriv f x ≤ 2) :
    ∀ x ≥ 0, x ≤ f x ∧ f x ≤ 2 * x := by
  intro x hx
  constructor
  -- Compare first with the identity function, whose derivative is constantly one.
  · have hid : Differentiable ℝ (fun y : ℝ => y) := differentiable_id
    have hderiv_id : ∀ y : ℝ, deriv (fun z : ℝ => z) y ≤ deriv f y := by
      intro y
      simpa using (hderiv y).1
    have hcompare := q5_deriv_comparison_on_ray hid hf (by simpa using hzero.symm) hderiv_id x hx
    simpa using hcompare
  -- Then compare with the line of slope two.
  · have hdouble : Differentiable ℝ (fun y : ℝ => 2 * y) := by fun_prop
    have hderiv_double : ∀ y : ℝ, deriv f y ≤ deriv (fun z : ℝ => 2 * z) y := by
      intro y
      simpa using (hderiv y).2
    have hcompare := q5_deriv_comparison_on_ray hf hdouble (by simpa using hzero) hderiv_double x hx
    simpa using hcompare


theorem q7_three_zeros_two_critical_points {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hcont : ContinuousOn f (Icc a c)) (hdiff : DifferentiableOn ℝ f (Ioo a c))
    (hfa : f a = 0) (hfb : f b = 0) (hfc : f c = 0) :
    ∃ u ∈ Ioo a b, deriv f u = 0 ∧ ∃ v ∈ Ioo b c, deriv f v = 0 := by
  -- Each neighboring pair of zeros supplies its own zero slope.
  have hcont_ab : ContinuousOn f (Icc a b) := hcont.mono fun x hx => ⟨hx.1, hx.2.trans hbc.le⟩
  have hdiff_ab : DifferentiableOn ℝ f (Ioo a b) := hdiff.mono fun x hx =>
    ⟨hx.1, hx.2.trans_le hbc.le⟩
  have hcont_bc : ContinuousOn f (Icc b c) := hcont.mono fun x hx => ⟨hab.le.trans hx.1, hx.2⟩
  have hdiff_bc : DifferentiableOn ℝ f (Ioo b c) := hdiff.mono fun x hx =>
    ⟨lt_of_lt_of_le hab hx.1.le, hx.2⟩
  obtain ⟨u, hu, huslope⟩ := exists_deriv_eq_slope f hab hcont_ab hdiff_ab
  obtain ⟨v, hv, hvslope⟩ := exists_deriv_eq_slope f hbc hcont_bc hdiff_bc
  refine ⟨u, hu, ?_, v, hv, ?_⟩
  · rw [hfa, hfb] at huslope
    simpa using huslope
  · rw [hfb, hfc] at hvslope
    simpa using hvslope


theorem q8_deriv_bound_is_contracting {f : ℝ → ℝ} {q : ℝ} (hf : Differentiable ℝ f)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : ∀ x : ℝ, |deriv f x| ≤ q) :
    ContractingWith q.toNNReal f := by
  -- The mean-value slope between two points is bounded by the derivative bound.
  have hforward : ∀ {x y : ℝ}, x < y → |f y - f x| ≤ q * |y - x| := by
    intro x y hxy
    have hcont : ContinuousOn f (Icc x y) := hf.continuous.continuousOn
    have hdiff : DifferentiableOn ℝ f (Ioo x y) := hf.differentiableOn
    obtain ⟨c, hc, hcslope⟩ := exists_deriv_eq_slope f hxy hcont hdiff
    have hratio : |(f y - f x) / (y - x)| ≤ q := by simpa [hcslope] using hderiv c
    rw [abs_div, abs_of_pos (sub_pos.mpr hxy)] at hratio
    simpa [abs_of_pos (sub_pos.mpr hxy)] using (div_le_iff₀ (sub_pos.mpr hxy)).mp hratio
  have hslope : ∀ {x y : ℝ}, |f y - f x| ≤ q * |y - x| := by
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · exact hforward hxy
    · simp
    · rw [abs_sub_comm]
      simpa [abs_sub_comm] using hforward hyx
  have hqcoe : (q.toNNReal : ℝ) = q := Real.coe_toNNReal q hq0
  have hcontract : ContractingWith q.toNNReal f := by
    constructor
    · exact (NNReal.coe_lt_coe).mpr (by simpa [hqcoe] using hq1)
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa [Real.dist_eq, hqcoe, abs_sub_comm] using hslope (x := x) (y := y)
  exact hcontract


theorem q9_contracting_fixed_point_and_iterates {f : ℝ → ℝ} {q : ℝ} (hf : Differentiable ℝ f)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : ∀ x : ℝ, |deriv f x| ≤ q) :
    ∃ p : ℝ, f p = p ∧ (∀ y : ℝ, f y = y → y = p) ∧
      ∀ x : ℝ, Tendsto (fun n : ℕ => f^[n] x) atTop (nhds p) := by
  -- Question 8 turns the derivative estimate into a global contraction.
  have hcontract := q8_deriv_bound_is_contracting hf hq0 hq1 hderiv
  -- Completeness then gives the fixed point and convergence of every iteration.
  let p : ℝ := ContractingWith.fixedPoint f hcontract
  refine ⟨p, ?_, ?_, ?_⟩
  · exact ContractingWith.fixedPoint_isFixedPt hcontract
  · intro y hy
    exact ContractingWith.fixedPoint_unique hcontract hy
  · exact ContractingWith.tendsto_iterate_fixedPoint hcontract


theorem q10_differentiable_damped_oscillation : HasDerivAt (dampedOscillation 2) 0 0 := by
  -- Division by the increment leaves one factor of the increment to control the sine.
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hε),
    self_mem_nhdsWithin] with t htball htne
  have ht0 : t ≠ 0 := htne
  have hslope : t⁻¹ • (dampedOscillation 2 (0 + t) - dampedOscillation 2 0) =
      t * Real.sin (1 / t) := by
    simp [dampedOscillation, ht0]
    field_simp
  rw [hslope, Real.dist_eq, sub_zero, abs_mul]
  have hsin : |Real.sin (1 / t)| ≤ 1 :=
    (abs_le).mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    |t| * |Real.sin (1 / t)| ≤ |t| * 1 :=
      mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
    _ < ε := by simpa [Real.dist_eq] using htball

end Solutions.Analysis.Differentiation
