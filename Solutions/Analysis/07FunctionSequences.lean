import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Solutions.Analysis.FunctionSequences

open Filter Set

def UniformlyConvergesOn (u : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - f x| < ε

noncomputable def powersLimit (x : ℝ) : ℝ := if x = 1 then 1 else 0

noncomputable def geometricPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ k

noncomputable def smoothAbs (n : ℕ) (x : ℝ) : ℝ :=
  √(x ^ 2 + 1 / ((n : ℝ) + 1))

theorem q1_powers_uniform_on_smaller_interval {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    UniformlyConvergesOn (fun n x => x ^ n) (fun _ => 0) (Icc 0 a) := by
  -- The scalar sequence `a^n` controls the error at every point of the interval.
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_pow_atTop_nhds_zero_of_lt_one ha₀ ha₁) ε hε
  refine ⟨N, fun n hn x hx => ?_⟩
  rw [sub_zero, abs_of_nonneg (pow_nonneg hx.1 _)]
  exact lt_of_le_of_lt (pow_le_pow_left₀ hx.1 hx.2 n)
    (by simpa [Real.dist_eq, abs_of_nonneg ha₀] using hN n hn)


theorem q2_powers_pointwise :
    ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => x ^ (n + 1)) atTop (nhds (powersLimit x)) := by
  intro x hx
  by_cases hx1 : x = 1
  · subst x
    simp [powersLimit]
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hxlt
    have hshift := hpow.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x))
    simpa [powersLimit, hx1, pow_succ, mul_comm] using hshift


theorem q3_powers_not_uniform :
    ¬ UniformlyConvergesOn (fun n x => x ^ (n + 1)) powersLimit (Icc 0 1) := by
  intro hunif
  obtain ⟨N, hN⟩ := hunif (1 / 4) (by norm_num)
  -- For every exponent, continuity produces a point where the power takes the middle value `1/2`.
  let p : ℝ → ℝ := fun x => x ^ (N + 1)
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  have hhalf : (1 / 2 : ℝ) ∈ p '' Icc (0 : ℝ) 1 := by
    apply intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hp.continuousOn
    dsimp [p]
    norm_num
  rcases hhalf with ⟨x, hx, hpx⟩
  have hx1 : x ≠ 1 := by
    intro hx1
    subst x
    norm_num [p] at hpx
  have herror := hN N le_rfl x hx
  dsimp [p] at hpx
  simp only [powersLimit, if_neg hx1] at herror
  rw [hpx] at herror
  norm_num at herror


theorem q4_uniform_limit_continuous_on {K : Set ℝ} {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hu : ∀ n, ContinuousOn (u n) K) (huf : UniformlyConvergesOn u f K) :
    ContinuousOn f K := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- `huf` supplies one index `N` whose error bound holds at both `x` and every nearby `y` in `K`.
  -- We then use the local continuity of this particular `u N` at `x` for the middle difference.
  obtain ⟨N, hN⟩ := huf (ε / 3) (by linarith)
  obtain ⟨δ, hδ, hlocal⟩ :=
    (Metric.continuousWithinAt_iff.mp ((hu N).continuousWithinAt hx)) (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  have hyN := hN N le_rfl y hy
  have hxN := hN N le_rfl x hx
  have hmiddle := hlocal hy hxy
  rw [Real.dist_eq] at hxy hmiddle ⊢
  calc
    |f y - f x| = |(f y - u N y) + (u N y - u N x) + (u N x - f x)| := by
      congr 1; ring
    _ ≤ |(f y - u N y) + (u N y - u N x)| + |u N x - f x| := abs_add_le _ _
    _ ≤ (|f y - u N y| + |u N y - u N x|) + |u N x - f x| := by
      gcongr
      exact abs_add_le _ _
    _ < ε := by
      rw [abs_sub_comm] at hyN
      linarith


theorem q5_geometric_function_series {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    UniformlyConvergesOn geometricPartialSum (fun x => 1 / (1 - x)) (Icc (-a) a) := by
  intro ε hε
  have hden : 0 < 1 - a := by linarith
  -- The geometric tail has size at most `a^n / (1-a)`, uniformly for `|x| ≤ a`.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha₀ ha₁) (ε * (1 - a)) (mul_pos hε hden)
  refine ⟨N, fun n hn x hx => ?_⟩
  have hxabs : |x| ≤ a := (abs_le).mpr hx
  have hxlt : x < 1 := lt_of_le_of_lt hx.2 ha₁
  have hxne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
  have hgeom : geometricPartialSum n x - 1 / (1 - x) = -(x ^ n / (1 - x)) := by
    dsimp [geometricPartialSum]
    have hsum := geom_sum_mul x n
    field_simp
    linarith
  rw [hgeom, abs_neg, abs_div, abs_pow, abs_of_pos (sub_pos.mpr hxlt)]
  have hpow : |x| ^ n ≤ a ^ n := pow_le_pow_left₀ (abs_nonneg x) hxabs n
  have hscalar : a ^ n < ε * (1 - a) := by
    simpa [Real.dist_eq, abs_of_nonneg ha₀, abs_of_nonneg (pow_nonneg ha₀ n)] using hN n hn
  calc
    |x| ^ n / (1 - x) ≤ a ^ n / (1 - a) :=
      div_le_div₀ (pow_nonneg ha₀ n) hpow hden (by linarith [hx.2])
    _ < ε := (div_lt_iff₀ hden).mpr hscalar


theorem q6_geometric_series_continuous {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    ContinuousOn (fun x => 1 / (1 - x)) (Icc (-a) a) := by
  -- The partial sums are polynomials, and q4 transfers their continuity to their uniform limit.
  apply q4_uniform_limit_continuous_on (u := geometricPartialSum)
  · intro n
    exact (continuous_finsetSum (Finset.range n) fun k _ => continuous_id.pow k).continuousOn
  · exact q5_geometric_function_series ha₀ ha₁


theorem q7_smooth_approximation_uniform :
    UniformlyConvergesOn smoothAbs (abs : ℝ → ℝ) (univ : Set ℝ) ∧
      ∀ n, Differentiable ℝ (smoothAbs n) := by
  constructor
  · intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
      (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun n hn x _ => ?_⟩
    let c : ℝ := 1 / ((n : ℝ) + 1)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hdenn : 0 ≤ (n : ℝ) + 1 := by positivity
    have hsmall : c < ε ^ 2 := by
      dsimp [c]
      simpa [Real.dist_eq, abs_of_nonneg hdenn] using hN n hn
    have hsqrt_small : √c < ε := (Real.sqrt_lt' hε).mpr hsmall
    -- Squaring shows that the smoothed value is trapped between `|x|` and `|x| + √c`.
    have hlower : |x| ≤ √(x ^ 2 + c) := by
      rw [← Real.sqrt_sq_eq_abs x]
      exact Real.sqrt_le_sqrt (by linarith [sq_nonneg x])
    have hupper_inside : x ^ 2 + c ≤ (|x| + √c) ^ 2 := by
      nlinarith [Real.sq_sqrt hc, sq_nonneg x, sq_abs x,
        mul_nonneg (abs_nonneg x) (Real.sqrt_nonneg c)]
    have hupper : √(x ^ 2 + c) ≤ |x| + √c := by
      have h := Real.sqrt_le_sqrt hupper_inside
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |x| + √c)] using h
    rw [smoothAbs]
    change abs (√(x ^ 2 + c) - |x|) < ε
    rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  · intro n x
    apply DifferentiableAt.sqrt
    · fun_prop
    · dsimp [smoothAbs]
      positivity


theorem q8_abs_not_differentiable_at_zero :
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) (0 : ℝ) := by
  intro h
  -- Right and left derivatives at zero would have to be `1` and `-1` simultaneously.
  have h₁ : deriv (abs : ℝ → ℝ) 0 = 1 :=
    (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h ↦ abs_of_nonneg h) Set.self_mem_Ici
  have h₂ : deriv (abs : ℝ → ℝ) 0 = -1 :=
    (uniqueDiffOn_Iic _ _ Set.self_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_neg _ _).congr_of_mem (fun _ h ↦ abs_of_nonpos h) Set.self_mem_Iic
  linarith

end Solutions.Analysis.FunctionSequences
