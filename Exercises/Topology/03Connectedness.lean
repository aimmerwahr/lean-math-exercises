import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Exercises — Topology / Connectedness

Connectedness says that a space cannot be split into two separated nonempty pieces. It is a
topological property: continuous images, products, and quotients preserve it, independently of
any metric. Intervals are the connected subsets of the real line, where this general idea becomes
the intermediate-value principle.

Prove each statement yourself; the canonical proofs live in
`Solutions/Topology/03Connectedness.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.Topology.Connectedness

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Connectedness consists of nonemptiness and the impossibility of a separation.
#check @IsConnected
#check @IsPreconnected

-- A continuous map pulls an open set back to an open set.
#check @Continuous.continuousOn

-- Images and unions of sets.
#check @Set.image_subset_iff
#check @IsPreconnected.union
#check @isPreconnected_Icc

end

/-- **Question 1.**

Every nonempty space with the indiscrete topology is connected. In particular, a two-point
indiscrete space is connected but not metrizable. -/
theorem q1_indiscrete_connected [Nonempty X] [IndiscreteTopology X] :
    IsConnected (Set.univ : Set X) := by
  sorry


/-- **Question 2.**

The image of a connected set under a continuous map is connected.

Prove without using `IsConnected.image`. -/
theorem q2_continuous_image_connected {s : Set X} (hs : IsConnected s) (f : X → Y)
    (hf : ContinuousOn f s) : IsConnected (f '' s) := by
  sorry


/-- **Question 3.**

If `S ⊆ X` and `T ⊆ Y` are connected, then `S × T` is connected in the product topology.

Prove without using `IsConnected.prod`. -/
theorem q3_connected_product {s : Set X} {t : Set Y} (hs : IsConnected s) (ht : IsConnected t) :
    IsConnected (s ×ˢ t) := by
  sorry


/-- **Question 4.**

The surjective quotient image of a connected space is connected.

Prove without using a packaged quotient-connectedness theorem. -/
theorem q4_quotient_connected {q : X → Y} (hq : Topology.IsQuotientMap q)
    (hX : IsConnected (Set.univ : Set X)) : IsConnected (Set.univ : Set Y) := by
  sorry


/-- **Question 5.**

If two closed real intervals have a common point, then their union is an interval and is
connected. -/
theorem q5_union_intervals_connected {a b c d : ℝ}
    (hcommon : (Set.Icc a b ∩ Set.Icc c d).Nonempty) :
    (Set.Icc a b ∪ Set.Icc c d).OrdConnected ∧ IsConnected (Set.Icc a b ∪ Set.Icc c d) := by
  sorry


/-- **Question 6.**

The punctured interval `(-1, 0) ∪ (0, 1)` is not connected. -/
theorem q6_punctured_interval_disconnected :
    ¬ IsConnected (Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1) := by
  sorry


/-- **Question 7.**

Every connected subset of `ℝ` is an interval. -/
theorem q7_connected_real_is_interval {s : Set ℝ} (hs : IsConnected s) : s.OrdConnected := by
  sorry


/-- **Question 8.**

If `f : ℝ → ℝ` is continuous on `[a,b]`, `a ≤ b`, and `u` lies between `f a` and `f b`, then
there is `c ∈ [a,b]` with `f c = u`.

Hint: apply Question 2 to the connected interval `[a,b]`. -/
theorem q8_intermediate_value {a b u : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hu : u ∈ Set.Icc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = u := by
  sorry


/-- **Question 9.**

If `f` is continuous on `[a,b]`, `a ≤ b`, `f a < 0`, and `0 < f b`, then `f` vanishes at a
point of `[a,b]`.

Hint: specialize Question 8 at `u = 0`. -/
theorem q9_sign_change_zero {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  sorry

end Exercises.Topology.Connectedness
