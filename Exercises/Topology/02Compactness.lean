import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Exercises — Topology / Compactness

Compactness turns infinitely many local choices into finitely many: every open cover of a compact
set has a finite subcover. In Euclidean space, compactness is equivalently closedness together with
boundedness. It persists under continuous maps and forces continuous real-valued functions to take
their extreme values. The same finite-control principle is the source of uniform continuity on a
compact domain and of compact neighborhoods in the real line.

Prove each statement yourself; the canonical proofs live in
`Solutions/Topology/02Compactness.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.Topology.Compactness

open Set Filter Uniformity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- The finite-subcover form of compactness.
#check @isCompact_iff_finite_subcover
#check @IsCompact.elim_finite_subcover

-- Closedness and boundedness in metric spaces.
#check @Metric.isCompact_iff_isClosed_bounded
#check @isClosed_Icc
#check @Metric.isBounded_Icc

-- Finite images and order extrema.
#check @ContinuousOn
#check @IsCompact.exists_isGreatest
#check @IsCompact.exists_isLeast

-- Uniform structures and metric neighborhoods.
#check @uniformContinuousOn_iff_restrict
#check @continuousOn_iff_continuous_restrict
#check @nhdsSet_diagonal_eq_uniformity
#check @Continuous.tendsto_nhdsSet
#check @nhdsSet_diagonal_le_uniformity
#check @Metric.mem_nhds_iff

end


/-- **Question 1.**

Every finite subset of a topological space is compact.

Prove without using `Set.Finite.isCompact`. -/
theorem q1_finite_compact {Z : Type*} [TopologicalSpace Z] {s : Set Z} (hs : s.Finite) :
    IsCompact s := by
  sorry


/-- **Question 2.**

Every closed interval `[a,b]` in `ℝ` is compact. Establish this through closedness and boundedness,
not by invoking interval compactness directly.

Prove without using `isCompact_Icc`. -/
theorem q2_closed_interval_compact (a b : ℝ) : IsCompact (Set.Icc a b) := by
  sorry


/-- **Question 3.**

If `K ⊆ X` is compact and `f` is continuous on `K`, then `f(K)` is compact.

Prove without using `IsCompact.image_of_continuousOn`. -/
theorem q3_compact_image {K : Set X} (hK : IsCompact K) {f : X → Y}
    (hf : ContinuousOn f K) : IsCompact (f '' K) := by
  sorry


/-- **Question 4.**

If `f : ℝ → ℝ` is continuous on `[a,b]` and `a ≤ b`, then `f` attains both a maximum and a
minimum on `[a,b]`.

Prove without using `IsCompact.exists_isMaxOn` or `IsCompact.exists_isMinOn`. -/
theorem q4_extreme_value {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f y ≤ f x) ∧
      ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x ≤ f y := by
  sorry


/-- **Question 5.**

A function continuous on a compact metric set is uniformly continuous there.

Prove without using `IsCompact.uniformContinuousOn_of_continuous` or
`CompactSpace.uniformContinuous_of_continuous`. -/
theorem q5_uniform_continuity_compact {K : Set X} (hK : IsCompact K) {f : X → Y}
    (hf : ContinuousOn f K) : UniformContinuousOn f K := by
  sorry


/-- **Question 6.**

If `U ⊆ ℝ` is open and contains `x`, then some compact closed interval centered at `x` is contained
in `U`. A space in which every point has a compact neighborhood is called locally compact; this
exercise verifies that property for `ℝ` explicitly.

Prove without using the `LocallyCompactSpace ℝ` instance. -/
theorem q6_real_compact_neighborhood {x : ℝ} {U : Set ℝ} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r > 0, IsCompact (Set.Icc (x - r) (x + r)) ∧ Set.Icc (x - r) (x + r) ⊆ U := by
  sorry

end Exercises.Topology.Compactness
