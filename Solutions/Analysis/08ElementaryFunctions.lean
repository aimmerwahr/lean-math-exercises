import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Solutions.Analysis.ElementaryFunctions

open Set


theorem q1_exp_tangent_bound (x : ℝ) :
    1 + x ≤ Real.exp x := by
  rcases le_total 0 x with hx | hx
  · rcases hx.eq_or_lt with rfl | hx
    · simp
    -- Between `0` and a positive point, the exponential has slope at least one.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope Real.exp hx
      Real.continuous_exp.continuousOn Real.differentiable_exp.differentiableOn
    have hslope' : Real.exp c = (Real.exp x - 1) / x := by
      simpa [Real.exp_zero] using hslope
    have hcexp : 1 ≤ Real.exp c := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hc.1.le
    have hratio : 1 ≤ (Real.exp x - 1) / x := by simpa [hslope'] using hcexp
    have hmul := (le_div_iff₀ hx).mp hratio
    linarith
  · rcases hx.eq_or_lt with rfl | hx
    · simp
    -- On the negative side, the same slope is at most one.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope Real.exp hx
      Real.continuous_exp.continuousOn Real.differentiable_exp.differentiableOn
    have hslope' : Real.exp c = (1 - Real.exp x) / (0 - x) := by
      simpa [Real.exp_zero] using hslope
    have hcexp : Real.exp c ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hc.2.le
    have hratio : (1 - Real.exp x) / (0 - x) ≤ 1 := by simpa [hslope'] using hcexp
    have hmul := (div_le_iff₀ (sub_pos.mpr hx)).mp hratio
    linarith


theorem q2_log_tangent_bound {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x - 1 := by
  -- Apply Question 1 at the logarithm, then use the inverse relation.
  have h := q1_exp_tangent_bound (Real.log x)
  rw [Real.exp_log hx] at h
  linarith


theorem q3_sin_lipschitz (x : ℝ) :
    |Real.sin x| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rcases hx.eq_or_lt with rfl | hx
    · simp
    -- The sine slope from zero is a cosine value, whose absolute value is at most one.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope Real.sin hx
      Real.continuous_sin.continuousOn Real.differentiable_sin.differentiableOn
    have hslope' : Real.cos c = Real.sin x / x := by
      simpa using hslope
    have hratio : |Real.sin x / x| ≤ 1 := by
      rw [← hslope']
      exact Real.abs_cos_le_one c
    rw [abs_div, abs_of_pos hx] at hratio
    simpa [abs_of_pos hx] using (div_le_iff₀ hx).mp hratio
  · rcases hx.eq_or_lt with rfl | hx
    · simp
    -- Reversing the interval gives the same estimate on the negative side.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope Real.sin hx
      Real.continuous_sin.continuousOn Real.differentiable_sin.differentiableOn
    have hslope' : Real.cos c = -Real.sin x / (0 - x) := by
      simpa using hslope
    have hratio : |-Real.sin x / (0 - x)| ≤ 1 := by
      rw [← hslope']
      exact Real.abs_cos_le_one c
    rw [abs_div, abs_neg, abs_of_pos (sub_pos.mpr hx)] at hratio
    simpa [abs_of_neg hx] using (div_le_iff₀ (sub_pos.mpr hx)).mp hratio


theorem q4_cos_quadratic_bound (x : ℝ) :
    1 - x ^ 2 / 2 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by
  -- Compare cosine with the quadratic lower candidate `1 - z² / 2`.
  let h : ℝ → ℝ := Real.cos - ((fun _ : ℝ => 1) - fun z : ℝ => (1 / 2) * z ^ 2)
  have hdiff : Differentiable ℝ h := by
    dsimp [h]
    fun_prop
  have hderiv : ∀ z : ℝ, deriv h z = z - Real.sin z := by
    intro z
    dsimp [h]
    have hz := (Real.hasDerivAt_cos z).sub
      ((hasDerivAt_const z (1 : ℝ)).sub (((hasDerivAt_id z).pow 2).const_mul (1 / 2)))
    have hderiv' : deriv (Real.cos - ((fun _ : ℝ => 1) - fun y : ℝ => (1 / 2) * y ^ 2)) z =
        -Real.sin z + z := by simpa [id] using hz.deriv
    linarith
  -- On the nonnegative ray, the sine estimate makes this difference have nonnegative slope.
  have hnonneg : ∀ z : ℝ, 0 ≤ z → 1 - z ^ 2 / 2 ≤ Real.cos z := by
    intro z hz
    rcases hz.eq_or_lt with rfl | hz
    · norm_num
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope h hz
      hdiff.continuous.continuousOn hdiff.differentiableOn
    have hderiv_nonneg : 0 ≤ deriv h c := by
      rw [hderiv]
      have hsin := q3_sin_lipschitz c
      rw [abs_of_nonneg hc.1.le] at hsin
      linarith [le_abs_self (Real.sin c)]
    have hratio : 0 ≤ (h z - h 0) / (z - 0) := by simpa [hslope] using hderiv_nonneg
    have hmul := mul_nonneg hratio (sub_pos.mpr hz).le
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hz))] at hmul
    dsimp [h] at hmul
    norm_num at hmul
    linarith
  constructor
  · have hlow := hnonneg |x| (abs_nonneg x)
    -- Cosine is even, so the estimate on the nonnegative ray covers every real input.
    have hcos : Real.cos |x| = Real.cos x := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_nonpos hx, Real.cos_neg]
    rw [sq_abs, hcos] at hlow
    exact hlow
  · have hsq : Real.cos x ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]
    nlinarith


theorem q5_log_difference_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ |x - y| / min x y := by
  -- First treat ordered endpoints; the other order follows by symmetry.
  have hordered : ∀ {u v : ℝ}, 0 < u → 0 < v → u ≤ v →
      |Real.log u - Real.log v| ≤ |u - v| / min u v := by
    intro u v hu hv huv
    rcases huv.eq_or_lt with rfl | huv
    · simp
    -- The mean-value slope is the reciprocal of a point between the endpoints.
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope Real.log huv
      (Real.continuousOn_log.mono (fun z hz => ne_of_gt (hu.trans_le hz.1)))
      (Real.differentiableOn_log.mono (fun z hz => ne_of_gt (hu.trans hz.1)))
    have hcpos : 0 < c := hu.trans hc.1
    have hslope' : c⁻¹ = (Real.log v - Real.log u) / (v - u) := by
      simpa using hslope
    have hlog : Real.log v - Real.log u = (v - u) / c := by
      field_simp [ne_of_gt hcpos, ne_of_gt huv] at hslope' ⊢
      linarith
    have hlognonpos : Real.log u - Real.log v ≤ 0 := by
      exact sub_nonpos.mpr (Real.log_le_log hu huv.le)
    rw [abs_of_nonpos hlognonpos, neg_sub, abs_sub_comm u v,
      abs_of_nonneg (sub_nonneg.mpr huv.le), min_eq_left huv.le, hlog,
      div_eq_mul_inv, div_eq_mul_inv]
    simpa [one_div] using
      (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hu hc.1.le)
        (sub_nonneg.mpr huv.le))
  rcases le_total x y with hxy | hyx
  · exact hordered hx hy hxy
  · simpa [abs_sub_comm, min_comm] using hordered hy hx hyx


theorem q6_binomial_approx_le_exp (n : ℕ) (hn : 0 < n) :
    (1 + (n : ℝ)⁻¹) ^ n ≤ Real.exp 1 := by
  -- Apply Question 1 to the increment `1 / n`, then multiply the `n` identical estimates.
  have hbase := q1_exp_tangent_bound ((n : ℝ)⁻¹)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (n : ℝ)⁻¹) hbase n
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  calc
    (1 + (n : ℝ)⁻¹) ^ n ≤ (Real.exp ((n : ℝ)⁻¹)) ^ n := hpow
    _ = Real.exp ((n : ℝ) * (n : ℝ)⁻¹) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp 1 := by rw [mul_inv_cancel₀ hn0]


theorem q7_exp_neg_difference_strict_mono :
    StrictMono (fun x : ℝ => x - Real.exp (-x)) := by
  intro u v huv
  let F : ℝ → ℝ := id - Real.exp ∘ Neg.neg
  change F u < F v
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hdiff : Differentiable ℝ F := by
    dsimp [F]
    fun_prop
  have hderiv : ∀ z : ℝ, deriv F z = 1 + Real.exp (-z) := by
    intro z
    dsimp [F]
    have hz := (hasDerivAt_id z).sub
      ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z))
    simpa using hz.deriv
  -- A positive derivative makes the difference strictly increasing.
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope F huv
    hcont.continuousOn hdiff.differentiableOn
  have hderivpos : 0 < deriv F c := by
    rw [hderiv]
    positivity
  have hratio : 0 < (F v - F u) / (v - u) := by simpa [hslope] using hderivpos
  have hmul := mul_pos hratio (sub_pos.mpr huv)
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt huv))] at hmul
  exact sub_pos.mp hmul


theorem q8_exp_neg_fixed_point :
    ∃! x : ℝ, x ∈ Ioo 0 1 ∧ Real.exp (-x) = x := by
  let F : ℝ → ℝ := fun z => z - Real.exp (-z)
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hnegexp : Real.exp (-1 : ℝ) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hF0 : F 0 < 0 := by
    dsimp [F]
    norm_num
  have hF1 : 0 < F 1 := by
    dsimp [F]
    linarith
  -- Continuity turns the endpoint sign change into a root.
  obtain ⟨r, hr, hrF⟩ := (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hcont.continuousOn) ⟨hF0.le, hF1.le⟩
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    linarith
  have hr1 : r ≠ 1 := by
    intro hr1
    subst r
    linarith
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
  have hrfix : Real.exp (-r) = r := by
    dsimp [F] at hrF
    linarith
  refine ⟨r, ⟨⟨hrpos, hrlt⟩, hrfix⟩, ?_⟩
  intro y hy
  -- Question 7 says that two zeroes of this strictly increasing function coincide.
  have hyF : F y = 0 := by
    dsimp [F]
    linarith [hy.2]
  apply q7_exp_neg_difference_strict_mono.injective
  change F y = F r
  rw [hyF, hrF]

end Solutions.Analysis.ElementaryFunctions
