import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Exercises — Analysis / RealSequences

A sequence records an indefinitely repeated process.  Convergence describes its eventual
behaviour, while subsequences isolate behaviour along selected indices.  Completeness and order
give particularly strong convergence principles for real sequences.

Prove each statement yourself; the canonical proofs live in
`Solutions/Analysis/02RealSequences.lean`. Do **not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular theorem. These bans are enforced
automatically when you build the project: if a proof uses a banned theorem (directly or through
automation), the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.Analysis.RealSequences

open Filter Set

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the
cursor on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Epsilon estimates and the Cauchy criterion.
#check @Metric.tendsto_atTop
#check @Metric.cauchySeq_iff

-- Archimedean choices used in explicit estimates.
#check @exists_nat_gt

-- Suprema and lower envelopes of tails.
#check @csSup_le
#check @le_csSup

-- Selecting and reindexing subsequences.
#check @Nat.exists_strictMono_subsequence
#check @StrictMono.tendsto_atTop

-- Passing a pointwise order bound to a limit.
#check @le_of_tendsto'

end


/-- **Question 1.**

The sequence `1 / (n + 1)` converges to `0` in `ℝ`.

Prove without using `tendsto_one_div_add_atTop_nhds_zero_nat`. -/
theorem q1_reciprocal_tends_to_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) := by
  sorry


/-- **Question 2.**

The sequence `(-1)^n` does not converge in `ℝ`. -/
theorem q2_alternating_sequence_not_convergent :
    ¬ ∃ p : ℝ, Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) atTop (nhds p) := by
  sorry


/-- **Question 3.**

If `0 ≤ r < 1`, then `r^n → 0` as `n → ∞`.

Prove without using `tendsto_pow_atTop_nhds_zero_of_lt_one`,
`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, or
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`. -/
theorem q3_geometric_tends_to_zero {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) := by
  sorry


/-- **Question 4.**

If a real sequence is nondecreasing and bounded above, it converges to the supremum of its
range.

Prove without using `tendsto_atTop_ciSup`. -/
theorem q4_monotone_tends_to_sup {u : ℕ → ℝ} (hu : Monotone u)
    (hbounded : BddAbove (range u)) :
    Tendsto u atTop (nhds (sSup (range u))) := by
  sorry


/-- **Question 5.**

The even and odd subsequences of `(-1)^n + 1 / (n + 1)` converge respectively to `1` and
`-1`. -/
theorem q5_even_odd_subsequence_limits :
    Tendsto (fun n : ℕ => (-1 : ℝ) ^ (2 * n) + 1 / (2 * n + 1)) atTop (nhds 1) ∧
      Tendsto (fun n : ℕ => (-1 : ℝ) ^ (2 * n + 1) + 1 / (2 * n + 2)) atTop (nhds (-1)) := by
  sorry


/-- **Question 6.**

Let `u` be a sequence in a metric space. If every subsequence of `u` has a further subsequence
converging to `p`, then `u` converges to `p`. Here a subsequence is indexed by a strictly
increasing map `ℕ → ℕ`.

Prove without using `Filter.tendsto_of_subseq_tendsto`. -/
theorem q6_subsequence_criterion_for_convergence {X : Type*} [MetricSpace X]
    {u : ℕ → X} {p : X}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ φ ∘ ψ) atTop (nhds p)) :
    Tendsto u atTop (nhds p) := by
  sorry


/-- The lower envelope of the tail of `u` beginning at `n`: the infimum of all values `u m`
with `n ≤ m`. -/
noncomputable def tailInf (u : ℕ → ℝ) (n : ℕ) : ℝ := sInf (u '' Set.Ici n)


/-- **Question 7.**

If a real sequence is bounded below, then the infima of its tails form a nondecreasing sequence. -/
theorem q7_tailInf_monotone {u : ℕ → ℝ} (hbounded : BddBelow (range u)) :
    Monotone (tailInf u) := by
  sorry


/-- **Question 8.**

Every Cauchy sequence of real numbers converges.

Hint: use Question 7 for the lower envelopes of the tails.

Prove without using `cauchySeq_tendsto_of_complete`, `CauchySeq.tendsto_limUnder`,
`cauchySeq_tendsto_of_isComplete`, or `tendsto_nhds_of_cauchySeq_of_subseq`. -/
theorem q8_cauchy_real_converges {u : ℕ → ℝ} (hu : CauchySeq u) :
    ∃ p : ℝ, Tendsto u atTop (nhds p) := by
  sorry


/-- **Question 9.**

Every real sequence has either a nondecreasing subsequence or a nonincreasing subsequence. -/
theorem q9_monotone_subsequence (u : ℕ → ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (u ∘ φ)) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Antitone (u ∘ φ) := by
  sorry


/-- **Question 10.**

Every bounded sequence of real numbers has a convergent subsequence.

Prove without using `tendsto_subseq_of_bounded` or
`tendsto_subseq_of_frequently_bounded`. -/
theorem q10_bolzano_weierstrass {u : ℕ → ℝ}
    (hbounded : ∃ M : ℝ, ∀ n : ℕ, |u n| ≤ M) :
    ∃ p : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (nhds p) := by
  sorry


/-- **Question 11.**

Every sequence with values in the closed interval `[a, b]` has a subsequence converging to a
point of `[a, b]`.

Prove without using `IsCompact.tendsto_subseq`, `IsCompact.tendsto_subseq'`, or
`IsSeqCompact.exists_tendsto`. -/
theorem q11_closed_interval_sequentially_compact {a b : ℝ} {u : ℕ → ℝ}
    (hu : ∀ n : ℕ, u n ∈ Set.Icc a b) :
    ∃ p ∈ Set.Icc a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (nhds p) := by
  sorry

end Exercises.Analysis.RealSequences
