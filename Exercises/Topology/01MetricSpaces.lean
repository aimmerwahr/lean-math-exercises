import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Exercises — Topology / MetricSpaces

A metric packages the idea of distance. Open balls define open and closed sets, convergence, and
continuity; these notions are stable under maps and products, rather than being accidents of the
real line. Metric spaces are the first setting in which the epsilon--delta language becomes a
portable mathematical tool.

Prove each statement yourself; the canonical proofs live in
`Solutions/Topology/01MetricSpaces.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.Topology.MetricSpaces

open Filter Set

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Open sets and the triangle inequality.
#check Metric.isOpen_iff
#check dist_triangle

-- Epsilon descriptions of sequential convergence and the Cauchy property.
#check Metric.tendsto_atTop
#check Metric.cauchySeq_iff

-- Converting a distance estimate into continuity.
#check LipschitzWith.of_dist_le_mul
#check LipschitzWith.continuous

-- The metric formulation of uniform continuity.
#check Metric.uniformContinuous_iff

end

/-- **Question 1.**

In a metric space, every open ball `B(x,r)` is open.

Prove without using `Metric.isOpen_ball`. -/
theorem q1_open_ball {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  sorry


/-- **Question 2.**

If `xₙ → x` and `xₙ → y` in a metric space, then `x = y`.

Prove without using `tendsto_nhds_unique`. -/
theorem q2_unique_limit {X : Type*} [MetricSpace X] {u : ℕ → X} {x y : X}
    (hx : Tendsto u atTop (nhds x)) (hy : Tendsto u atTop (nhds y)) : x = y := by
  sorry


/-- **Question 3.**

For maps between metric spaces, `f` is continuous if and only if `xₙ → x` implies
`f(xₙ) → f(x)`.

Prove without using `continuous_iff_seqContinuous`. -/
theorem q3_continuous_iff_seqContinuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Continuous f ↔ SeqContinuous f := by
  sorry


/-- **Question 4.**

For `x, y ∈ ℝ`, `||x| - |y|| ≤ |x-y|`; deduce that `x ↦ |x|` is continuous.

Prove without using `continuous_abs`. -/
theorem q4_abs_lipschitz :
    (∀ x y : ℝ, |(|x| - |y|)| ≤ |x - y|) ∧ Continuous (fun x : ℝ => |x|) := by
  sorry


/-- **Question 5.**

For every `a ∈ ℝ`, the map `x ↦ x²` is continuous at `a`.

Prove without using `continuousAt_pow` or `continuous_pow`. -/
theorem q5_square_continuous_at (a : ℝ) : ContinuousAt (fun x : ℝ => x ^ 2) a := by
  sorry


/-- **Question 6.**

If `g : X → Y` is uniformly continuous between metric spaces and `(xₙ)` is Cauchy in `X`, then
`(g(xₙ))` is Cauchy in `Y`.

Prove without using `UniformContinuous.comp_cauchySeq`. -/
theorem q6_uniform_continuous_cauchy {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (g : X → Y) (hg : UniformContinuous g) {u : ℕ → X} (hu : CauchySeq u) :
    CauchySeq (g ∘ u) := by
  sorry

end Exercises.Topology.MetricSpaces
