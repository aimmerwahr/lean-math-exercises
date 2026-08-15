import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace Solutions.Topology.MetricSpaces

open Filter Set


theorem q1_open_ball {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  -- Around a point already inside the ball, the unused part of the radius is positive.
  rw [Metric.isOpen_iff]
  intro y hy
  rw [Metric.mem_ball] at hy
  refine ⟨r - dist y x, sub_pos.mpr hy, ?_⟩
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ < (r - dist y x) + dist y x := by linarith
    _ = r := sub_add_cancel _ _


theorem q2_unique_limit {X : Type*} [MetricSpace X] {u : ℕ → X} {x y : X}
    (hx : Tendsto u atTop (nhds x)) (hy : Tendsto u atTop (nhds y)) : x = y := by
  -- If two proposed limits were apart, a sufficiently late term would have to be too close to both.
  by_contra hxy
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hx) (dist x y / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hy) (dist x y / 3) (by linarith)
  let N := max N₁ N₂
  have hxN : dist (u N) x < dist x y / 3 := hN₁ N (le_max_left _ _)
  have hyN : dist (u N) y < dist x y / 3 := hN₂ N (le_max_right _ _)
  have htriangle : dist x y ≤ dist x (u N) + dist (u N) y := dist_triangle _ _ _
  rw [dist_comm x (u N)] at htriangle
  linarith


theorem q3_continuous_iff_seqContinuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Continuous f ↔ SeqContinuous f := by
  constructor
  · intro hf u x hu
    exact (hf.tendsto x).comp hu
  · intro hf
    -- In a metric space, a set is closed precisely when it contains the limits of all of
    -- its convergent sequences. Pulling such a set back preserves this property.
    apply continuous_iff_isClosed.mpr
    intro s hs
    exact (hs.isSeqClosed.preimage hf).isClosed


theorem q4_abs_lipschitz :
    (∀ x y : ℝ, |(|x| - |y|)| ≤ |x - y|) ∧ Continuous (fun x : ℝ => |x|) := by
  -- The reverse triangle inequality makes absolute value a distance-nonincreasing map.
  have hreverse : ∀ x y : ℝ, |(|x| - |y|)| ≤ |x - y| := by
    intro x y
    rw [abs_sub_le_iff]
    constructor
    · exact abs_sub_abs_le_abs_sub x y
    · have h := abs_sub_abs_le_abs_sub y x
      have habs : |y - x| = |x - y| := abs_sub_comm y x
      linarith
  have hlip : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hreverse x y
  exact ⟨hreverse, hlip.continuous⟩


theorem q5_square_continuous_at (a : ℝ) : ContinuousAt (fun x : ℝ => x ^ 2) a := by
  -- First keep `x` within one unit of `a`; then the second factor in the difference of
  -- squares has a fixed bound.
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := min 1 (ε / (2 * |a| + 1))
  have hden : 0 < 2 * |a| + 1 := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx ⊢
  have hxa : |x - a| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx_bound : |x| ≤ |a| + 1 := by
    calc
      |x| = |(x - a) + a| := by ring_nf
      _ ≤ |x - a| + |a| := abs_add_le _ _
      _ ≤ |a| + 1 := by linarith
  have hsum : |x + a| ≤ 2 * |a| + 1 := by
    calc
      |x + a| ≤ |x| + |a| := abs_add_le _ _
      _ ≤ 2 * |a| + 1 := by linarith
  have hmain : |x - a| * (2 * |a| + 1) < ε := by
    have hδle : δ ≤ ε / (2 * |a| + 1) := min_le_right _ _
    have hδmul : δ * (2 * |a| + 1) ≤ ε := (le_div_iff₀ hden).mp hδle
    exact (mul_lt_mul_of_pos_right hx hden).trans_le hδmul
  calc
    |x ^ 2 - a ^ 2| = |(x - a) * (x + a)| := by ring_nf
    _ = |x - a| * |x + a| := abs_mul _ _
    _ ≤ |x - a| * (2 * |a| + 1) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ < ε := hmain


theorem q6_uniform_continuous_cauchy {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (g : X → Y) (hg : UniformContinuous g) {u : ℕ → X} (hu : CauchySeq u) :
    CauchySeq (g ∘ u) := by
  -- One input tolerance works for every pair of sufficiently late terms.
  rw [Metric.cauchySeq_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, huniform⟩ := (Metric.uniformContinuous_iff.mp hg) ε hε
  obtain ⟨N, hN⟩ := hu δ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn
  exact huniform (hN m hm n hn)

end Solutions.Topology.MetricSpaces
