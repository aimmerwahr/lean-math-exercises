import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Exercises — Analysis / ContinuousFunctions

Continuity formalizes the principle that small changes of input cause small changes of output.
For real functions, this local condition combines with the order of the line to produce global
consequences: a continuous function carries an interval through every intermediate height, and a
self-map of a closed interval has a fixed point. On a bounded interval, estimates can be made
uniform in the input; at a singular-looking point, a sufficiently strong estimate can still force
continuity.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/04ContinuousFunctions.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular theorem. These bans are enforced
automatically when you build the project: if a proof uses a banned theorem (directly or through
automation), the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.Analysis.ContinuousFunctions

open Filter Set

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Epsilon--delta continuity in a metric space.
#check @Metric.continuousAt_iff

-- Functions that agree with a familiar formula in a neighborhood.
#check @eventually_lt_nhds
#check @eventually_gt_nhds
#check @continuousAt_pow

-- Continuity of algebraic combinations on a set.
#check @ContinuousOn.sub
#check @continuousOn_id

-- The intermediate-value principle on a closed interval.
#check @intermediate_value_Icc

-- Elementary bounds for sine.
#check @Real.neg_one_le_sin
#check @Real.sin_le_one

end

/-- The function which agrees with `x²` on the nonpositive half-line and with `x` on the positive
half-line. The two formulas have the same value at `0`. -/
noncomputable def matchingPiecewise (x : ℝ) : ℝ := if x ≤ 0 then x ^ 2 else x


/-- **Question 1.**

The matching piecewise function is continuous at every real number. In particular, the two pieces
fit continuously at `0`.

Prove without using `continuous_if_le` or `Continuous.if_le`. -/
theorem q1_matching_piecewise_continuous : Continuous matchingPiecewise := by
  sorry


/-- **Question 2.**

For every `M ≥ 0`, the square function has the following explicit uniform-continuity modulus on
`[-M,M]`: whenever `|x-y| < ε/(2M+1)` and both `x` and `y` lie in the interval, then
`|x²-y²| < ε`.

-/

theorem q2_square_uniform_on_interval {M ε x y : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hx : x ∈ Icc (-M) M) (hy : y ∈ Icc (-M) M)
    (hxy : |x - y| < ε / (2 * M + 1)) : |x ^ 2 - y ^ 2| < ε := by
  sorry


/-- **Question 3.**

If a continuous real function maps `[0,1]` into itself, then it has a fixed point in `[0,1]`.

Prove without using `exists_mem_Icc_isFixedPt`. -/
theorem q3_interval_self_map_fixed_point (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (hself : MapsTo f (Icc 0 1) (Icc 0 1)) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = x := by
  sorry


/-- **Question 4.**

If a continuous real function has equal values at `0` and `2`, then at two points a distance
`1` apart it has the same value. More precisely, there is an `x ∈ [0,1]` with
`f x = f (x + 1)`. -/
theorem q4_shifted_equal_values (f : ℝ → ℝ) (hf : Continuous f) (hends : f 0 = f 2) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = f (x + 1) := by
  sorry


/-- For every positive `n`, the damped oscillation `xⁿ sin(1/x)`, extended by the value `0` at the
origin. Although the oscillation becomes arbitrarily rapid near `0`, its amplitude tends to zero.
The definition also accepts `n = 0`, which is the undamped and discontinuous case; it is not used
in these sheets. In particular, `dampedOscillation 1` is `x sin(1/x)`. -/
noncomputable def dampedOscillation (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ n * Real.sin (1 / x)


/-- **Question 5.**

The damped oscillation `dampedOscillation 1` is continuous at `0`. -/
theorem q5_damped_oscillation_continuous : ContinuousAt (dampedOscillation 1) 0 := by
  sorry

end Exercises.Analysis.ContinuousFunctions
