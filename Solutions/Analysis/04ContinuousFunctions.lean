import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Solutions.Analysis.ContinuousFunctions

open Filter Set


noncomputable def matchingPiecewise (x : ℝ) : ℝ := if x ≤ 0 then x ^ 2 else x


theorem q1_matching_piecewise_continuous : Continuous matchingPiecewise := by
  rw [continuous_iff_continuousAt]
  intro a
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · -- Strictly to the left of the join, the function agrees locally with the square map.
    refine (continuousAt_pow a 2).congr ?_
    filter_upwards [eventually_lt_nhds ha] with x hx
    simp [matchingPiecewise, hx.le]
  · -- At the join, the left-hand square is bounded by `|x|` near zero.
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
    intro x hx
    rw [Real.dist_eq] at hx ⊢
    have hx1 : |x| < 1 := lt_of_lt_of_le (by simpa using hx) (min_le_left _ _)
    have hxε : |x| < ε := lt_of_lt_of_le (by simpa using hx) (min_le_right _ _)
    simp only [matchingPiecewise, if_pos (le_refl (0 : ℝ))]
    split_ifs with hx0
    · have hrewrite : |x ^ 2 - 0 ^ 2| = |x| ^ 2 := by norm_num [abs_pow]
      rw [hrewrite]
      have hsq : |x| ^ 2 ≤ |x| := by nlinarith [abs_nonneg x]
      exact hsq.trans_lt hxε
    · simpa using hxε
  · -- Strictly to the right of the join, the function agrees locally with the identity map.
    refine continuousAt_id.congr ?_
    filter_upwards [eventually_gt_nhds ha] with x hx
    simp [matchingPiecewise, not_le_of_gt hx]


theorem q2_square_uniform_on_interval {M ε x y : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hx : x ∈ Icc (-M) M) (hy : y ∈ Icc (-M) M)
    (hxy : |x - y| < ε / (2 * M + 1)) : |x ^ 2 - y ^ 2| < ε := by
  -- On this interval the second factor in `x² - y² = (x-y)(x+y)` is uniformly bounded.
  have hx_abs : |x| ≤ M := (abs_le).mpr hx
  have hy_abs : |y| ≤ M := (abs_le).mpr hy
  have hsum : |x + y| ≤ 2 * M + 1 := by
    calc
      |x + y| ≤ |x| + |y| := abs_add_le _ _
      _ ≤ 2 * M + 1 := by linarith
  have hden : 0 < 2 * M + 1 := by linarith
  have hmain : |x - y| * (2 * M + 1) < ε := by
    calc
      |x - y| * (2 * M + 1) < (ε / (2 * M + 1)) * (2 * M + 1) :=
        mul_lt_mul_of_pos_right hxy hden
      _ = ε := by field_simp
  calc
    |x ^ 2 - y ^ 2| = |(x - y) * (x + y)| := by ring_nf
    _ = |x - y| * |x + y| := abs_mul _ _
    _ ≤ |x - y| * (2 * M + 1) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ < ε := hmain


theorem q3_interval_self_map_fixed_point (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (hself : MapsTo f (Icc 0 1) (Icc 0 1)) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = x := by
  -- The displacement `x - f(x)` is nonpositive at the left endpoint and nonnegative at the
  -- right endpoint, so it vanishes somewhere between them.
  let g : ℝ → ℝ := fun x => x - f x
  have hg : ContinuousOn g (Icc 0 1) := by
    change ContinuousOn (id - f) (Icc 0 1)
    exact continuousOn_id.sub hf
  have hf0 : f 0 ∈ Icc (0 : ℝ) 1 := hself (by norm_num)
  have hf1 : f 1 ∈ Icc (0 : ℝ) 1 := hself (by norm_num)
  rcases hf0 with ⟨hf0, _⟩
  rcases hf1 with ⟨_, hf1⟩
  have hzero : (0 : ℝ) ∈ Icc (g 0) (g 1) := by
    dsimp [g]
    constructor <;> linarith
  rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg hzero with ⟨x, hx, hxg⟩
  refine ⟨x, hx, ?_⟩
  dsimp [g] at hxg
  linarith


theorem q4_shifted_equal_values (f : ℝ → ℝ) (hf : Continuous f) (hends : f 0 = f 2) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = f (x + 1) := by
  -- Compare the values one unit apart.  The endpoint values of this difference have opposite
  -- signs because `f 0 = f 2`.
  let g : ℝ → ℝ := fun x => f (x + 1) - f x
  have hg : Continuous g := by
    dsimp [g]
    exact (hf.comp (continuous_id.add continuous_const)).sub hf
  have hsum : g 0 + g 1 = 0 := by
    dsimp [g]
    rw [hends]
    ring_nf
  by_cases hg0 : g 0 ≤ 0
  · have hg1 : 0 ≤ g 1 := by linarith
    have hzero : (0 : ℝ) ∈ Icc (g 0) (g 1) := ⟨hg0, hg1⟩
    rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn hzero with
      ⟨x, hx, hxg⟩
    refine ⟨x, hx, ?_⟩
    dsimp [g] at hxg
    linarith
  · -- If the endpoint signs occur in the other order, negate the difference before applying IVT.
    let h : ℝ → ℝ := fun x => -g x
    have hh : Continuous h := hg.neg
    have hh0 : h 0 ≤ 0 := by
      dsimp [h]
      linarith
    have hh1 : 0 ≤ h 1 := by
      dsimp [h]
      linarith
    have hzero : (0 : ℝ) ∈ Icc (h 0) (h 1) := ⟨hh0, hh1⟩
    rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hh.continuousOn hzero with
      ⟨x, hx, hxh⟩
    refine ⟨x, hx, ?_⟩
    dsimp [h] at hxh
    dsimp [g] at hxh
    linarith


noncomputable def dampedOscillation (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ n * Real.sin (1 / x)


theorem q5_damped_oscillation_continuous : ContinuousAt (dampedOscillation 1) 0 := by
  -- The sine factor is always between `-1` and `1`, so the oscillation has size at most `|x|`.
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx ⊢
  by_cases hx0 : x = 0
  · subst x
    simp [dampedOscillation]
    exact hε
  · have hsin : |Real.sin (1 / x)| ≤ 1 :=
      (abs_le).mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have hx_abs : |x| < ε := by simpa using hx
    have hprod : |x| * 1 < ε := by simpa using hx_abs
    simpa [dampedOscillation, hx0] using
      (show |x| * |Real.sin (1 / x)| < ε from
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsin (abs_nonneg _)) hprod)

end Solutions.Analysis.ContinuousFunctions
