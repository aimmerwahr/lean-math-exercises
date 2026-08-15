import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Exercises — Analysis / OrderCompleteness

The distinctive property of the real line is completeness: a nonempty set bounded above has a
least upper bound. It turns order information into existence statements, explains why Cauchy and
monotone processes have limits, and separates `ℝ` from `ℚ`. The Archimedean property and density
of rationals give the accompanying discrete approximations to a continuous line.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/01OrderCompleteness.lean`. Do **not** commit your proofs into this file.
-/

namespace Exercises.Analysis.OrderCompleteness

open Filter Set

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Integer bracketing and casts.
#check @Int.floor_le
#check @Int.lt_floor_add_one

-- The two defining inequalities for a supremum.
#check @le_csSup
#check @csSup_le

-- Shrinking intervals and convergence.
#check @Metric.tendsto_atTop

end

/-- **Question 1.**

Every `x ∈ ℝ` can be written uniquely as `x = z + u`, where `z ∈ ℤ` and `0 ≤ u < 1`. -/
theorem q1_integer_fractional_decomposition (x : ℝ) :
    ∃! p : ℤ × ℝ, x = (p.1 : ℝ) + p.2 ∧ 0 ≤ p.2 ∧ p.2 < 1 := by
  sorry


/-- **Question 2.**

For every `x ∈ ℝ`, there exists `n ∈ ℕ` such that `x < n`.

Prove without using `exists_nat_gt`. -/
theorem q2_naturals_unbounded (x : ℝ) : ∃ n : ℕ, x < n := by
  sorry


/-- **Question 3.**

For every `ε > 0`, there exists `n ∈ ℕ` with `0 < n` and `1/n < ε`.

Prove without using `tendsto_one_div_atTop_nhds_zero_nat`. -/
theorem q3_archimedean_reciprocal {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / (n : ℝ) < ε := by
  sorry


/-- **Question 4.**

If `x < y` in `ℝ`, there exists `q ∈ ℚ` with `x < q < y`.

Prove without using `exists_rat_btwn`. -/
theorem q4_rational_between {x y : ℝ} (hxy : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := by
  sorry


/-- **Question 5.**

For `x ∈ ℝ` and `ε > 0`, there exists `q ∈ ℚ` such that `|x - q| < ε`.

Prove without using `Rat.denseRange_cast`. -/
theorem q5_rational_approximation (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, |x - (q : ℝ)| < ε := by
  sorry


/-- **Question 6.**

If `A ⊆ ℝ` is nonempty and bounded above, then for every `ε > 0` there is `a ∈ A` with
`sup A - ε < a`.

Prove without using `lt_csSup_iff`. -/
theorem q6_sup_approximation {A : Set ℝ} (hA : A.Nonempty) (_hAb : BddAbove A) {ε : ℝ}
    (hε : 0 < ε) : ∃ a ∈ A, sSup A - ε < a := by
  sorry


/-- **Question 7.**

If `A ⊆ ℝ` is nonempty and bounded above, then
`sup {t + a | a ∈ A} = t + sup A`.

Prove without using `csSup_add`. -/
theorem q7_sup_translate {A : Set ℝ} (hA : A.Nonempty) (hAb : BddAbove A) (t : ℝ) :
    sSup {x | ∃ a ∈ A, x = t + a} = t + sSup A := by
  sorry


/-- **Question 8.**

If `A, B ⊆ ℝ` are nonempty and bounded above, then
`sup {a + b | a ∈ A, b ∈ B} = sup A + sup B`.

Prove without using `csSup_add`. -/
theorem q8_sup_sumset {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) (hAb : BddAbove A)
    (hBb : BddAbove B) :
    sSup {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b} = sSup A + sSup B := by
  sorry


/-- The nonnegative real numbers whose square is strictly below `2`. -/
def sqrtTwoSet : Set ℝ := {x | 0 ≤ x ∧ x ^ 2 < 2}

/-- **Question 9.**

For `S = {x ∈ ℝ | 0 ≤ x ∧ x² < 2}`, prove that `S` is nonempty and bounded above. -/
theorem q9_sqrtTwoSet_nonempty_bddAbove : sqrtTwoSet.Nonempty ∧ BddAbove sqrtTwoSet := by
  sorry


/-- **Question 10.**

Let `s = sup S`, where `S = {x ∈ ℝ | 0 ≤ x ∧ x² < 2}`. Prove that `s² < 2` is impossible.

Prove without using `Real.sq_sqrt` or `Real.sqrt_sq`. -/
theorem q10_sSup_sqrtTwoSet_sq_not_lt : ¬ sSup sqrtTwoSet ^ 2 < 2 := by
  sorry


/-- **Question 11.**

Let `s = sup S`, where `S = {x ∈ ℝ | 0 ≤ x ∧ x² < 2}`. Prove that `2 < s²` is impossible.

Prove without using `Real.sq_sqrt` or `Real.sqrt_sq`. -/
theorem q11_sSup_sqrtTwoSet_sq_not_gt : ¬ 2 < sSup sqrtTwoSet ^ 2 := by
  sorry


/-- **Question 12.**

Let `S = {x ∈ ℝ | 0 ≤ x ∧ x² < 2}` and let `s = sup S`. Prove `s² = 2`.

Prove without using `Real.sq_sqrt` or `Real.sqrt_sq`. -/
theorem q12_square_root_two_from_supremum : sSup sqrtTwoSet ^ 2 = 2 := by
  sorry


/-- **Question 13.**

Let `(aₙ)` be nondecreasing and `(bₙ)` nonincreasing, with `aₙ ≤ bₙ` for all `n`. Prove that
`⋂ n, [aₙ, bₙ]` is nonempty.

Prove without using `Monotone.ciSup_mem_iInter_Icc_of_antitone` or
`ciSup_mem_iInter_Icc_of_antitone_Icc`. -/
theorem q13_nested_intervals_nonempty {a b : ℕ → ℝ} (ha : Monotone a) (hb : Antitone b)
    (hab : ∀ n, a n ≤ b n) :
    ∃ x : ℝ, x ∈ ⋂ n, Set.Icc (a n) (b n) := by
  sorry


/-- **Question 14.**

If `bₙ - aₙ → 0`, then `⋂ n, [aₙ, bₙ]` contains at most one point. -/
theorem q14_nested_intervals_unique {a b : ℕ → ℝ}
    (hshrink : Tendsto (fun n => b n - a n) atTop (nhds 0)) {x y : ℝ}
    (hx : x ∈ ⋂ n, Set.Icc (a n) (b n)) (hy : y ∈ ⋂ n, Set.Icc (a n) (b n)) : x = y := by
  sorry

end Exercises.Analysis.OrderCompleteness
