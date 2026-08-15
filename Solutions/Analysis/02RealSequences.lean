import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace Solutions.Analysis.RealSequences

open Filter Set


theorem q1_reciprocal_tends_to_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) := by
  -- An index larger than the reciprocal of the requested error makes every later denominator
  -- large enough.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hNε : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    nlinarith
  · positivity


theorem q2_alternating_sequence_not_convergent :
    ¬ ∃ p : ℝ, Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) atTop (nhds p) := by
  rintro ⟨p, hp⟩
  -- A single small neighbourhood of a hypothetical limit would have to contain both parities.
  rw [Metric.tendsto_atTop] at hp
  obtain ⟨N, hN⟩ := hp (1 / 2) (by norm_num)
  have heven := hN (2 * N) (by omega)
  have hodd := hN (2 * N + 1) (by omega)
  have heven' : dist (1 : ℝ) p < 1 / 2 := by
    simpa [Real.dist_eq, pow_mul] using heven
  have hodd' : dist (-1 : ℝ) p < 1 / 2 := by
    simpa [Real.dist_eq, pow_mul, pow_succ] using hodd
  -- The triangle inequality would then force the two distinct values `1` and `-1` to be closer
  -- than their actual distance.
  have htwo : (2 : ℝ) < 1 := calc
    (2 : ℝ) = dist (1 : ℝ) (-1) := by norm_num [Real.dist_eq]
    _ ≤ dist (1 : ℝ) p + dist p (-1) := dist_triangle _ _ _
    _ = dist (1 : ℝ) p + dist (-1 : ℝ) p := by rw [dist_comm p]
    _ < 1 := by linarith
  norm_num at htwo


theorem q3_geometric_tends_to_zero {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) := by
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := lt_of_le_of_ne hr₀ (Ne.symm hr)
  let a : ℝ := r⁻¹ - 1
  have ha : 0 < a := by
    dsimp [a]
    linarith [(one_lt_inv₀ hrpos).mpr hr₁]
  -- Writing `r⁻¹ = 1 + a` exposes the positive gap from `1`; Bernoulli's inequality then turns
  -- exponential decay into a reciprocal estimate.
  have hpower : ∀ n : ℕ, r ^ n ≤ 1 / (1 + n * a) := by
    intro n
    have hden : 0 < 1 + n * a := by positivity
    have hbernoulli : 1 + n * a ≤ (1 + a) ^ n :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ a) n
    have hinv : 1 + a = r⁻¹ := by simp [a]
    calc
      r ^ n = 1 / ((r⁻¹) ^ n) := by simp [inv_pow]
      _ ≤ 1 / (1 + n * a) := one_div_le_one_div_of_le hden (by simpa [hinv] using hbernoulli)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (a * ε))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · refine lt_of_le_of_lt (hpower n) ?_
    apply (div_lt_iff₀ (by positivity : 0 < 1 + n * a)).mpr
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hNε : 1 < (N : ℝ) * (a * ε) := (div_lt_iff₀ (mul_pos ha hε)).mp hN
    have hmul : (N : ℝ) * (a * ε) ≤ (n : ℝ) * (a * ε) :=
      mul_le_mul_of_nonneg_right hNn (le_of_lt (mul_pos ha hε))
    nlinarith
  · positivity


theorem q4_monotone_tends_to_sup {u : ℕ → ℝ} (hu : Monotone u)
    (hbounded : BddAbove (range u)) :
    Tendsto u atTop (nhds (sSup (range u))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hne : (range u).Nonempty := ⟨u 0, ⟨0, rfl⟩⟩
  have hsup : ∀ n, u n ≤ sSup (range u) := fun n => le_csSup hbounded ⟨n, rfl⟩
  -- If no term approached the supremum from below, a smaller number would already be an upper bound.
  have hnear : ∃ N, sSup (range u) - ε < u N := by
    by_contra h
    push Not at h
    have hupper : sSup (range u) ≤ sSup (range u) - ε :=
      csSup_le hne fun x hx => by rcases hx with ⟨n, rfl⟩; exact h n
    linarith
  obtain ⟨N, hN⟩ := hnear
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_of_nonpos]
  · have hlow : sSup (range u) - ε < u n := lt_of_lt_of_le hN (hu hn)
    linarith [hsup n]
  · exact sub_nonpos.mpr (hsup n)


theorem q5_even_odd_subsequence_limits :
    Tendsto (fun n : ℕ => (-1 : ℝ) ^ (2 * n) + 1 / (2 * n + 1)) atTop (nhds 1) ∧
      Tendsto (fun n : ℕ => (-1 : ℝ) ^ (2 * n + 1) + 1 / (2 * n + 2)) atTop (nhds (-1)) := by
  -- Restrict the reciprocal limit to each parity class.
  have heven_index : StrictMono (fun n : ℕ => 2 * n) := by
    intro m n hmn
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr hmn
  have hodd_index : StrictMono (fun n : ℕ => 2 * n + 1) := by
    intro m n hmn
    exact Nat.add_lt_add_right ((Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr hmn) 1
  have heven_reciprocal := q1_reciprocal_tends_to_zero.comp heven_index.tendsto_atTop
  have hodd_reciprocal := q1_reciprocal_tends_to_zero.comp hodd_index.tendsto_atTop
  constructor
  · simpa [pow_mul] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add heven_reciprocal)
  · have hsum :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds (-1))).add hodd_reciprocal
    -- The remaining work is only to identify the odd power and its reindexed denominator.
    have hrewrite :
        (fun n : ℕ => (-1 : ℝ) ^ (2 * n + 1) + 1 / (2 * n + 2)) =
          fun n => (-1 : ℝ) + 1 / ((2 * n + 1 : ℕ) + 1) := by
      funext n
      have hpow : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
        rw [pow_add, pow_mul]
        norm_num
      rw [hpow]
      congr 1
      norm_cast
    rw [hrewrite]
    simpa [Function.comp_apply] using hsum


theorem q6_subsequence_criterion_for_convergence {X : Type*} [MetricSpace X]
    {u : ℕ → X} {p : X}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ φ ∘ ψ) atTop (nhds p)) :
    Tendsto u atTop (nhds p) := by
  rw [Metric.tendsto_atTop]
  by_contra hconv
  push Not at hconv
  obtain ⟨ε, hε, hfar⟩ := hconv
  -- Failure of convergence supplies infinitely many terms outside one fixed ball about `p`.
  have hselect : ∀ N : ℕ, ∃ n > N, ε ≤ dist (u n) p := by
    intro N
    obtain ⟨n, hn, hdist⟩ := hfar (N + 1)
    exact ⟨n, by omega, hdist⟩
  obtain ⟨φ, hφmono, hφfar⟩ := Nat.exists_strictMono_subsequence hselect
  obtain ⟨ψ, hψmono, hlim⟩ := h φ hφmono
  -- This further subsequence remains outside the chosen ball, contradicting its convergence to `p`.
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  have htoo_close := hN N le_rfl
  have htoo_far := hφfar (ψ N)
  exact (not_lt_of_ge htoo_far) (by simpa [Function.comp_def] using htoo_close)


noncomputable def tailInf (u : ℕ → ℝ) (n : ℕ) : ℝ := sInf (u '' Set.Ici n)


theorem q7_tailInf_monotone {u : ℕ → ℝ} (hbounded : BddBelow (range u)) :
    Monotone (tailInf u) := by
  -- A later tail has fewer values, so its infimum cannot lie below the earlier tail infimum.
  intro n m hnm
  dsimp [tailInf]
  apply csInf_le_csInf ?_ ?_ ?_
  · rcases hbounded with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro x ⟨k, hk, rfl⟩
    exact hb ⟨k, rfl⟩
  · exact ⟨u m, ⟨m, by simp, rfl⟩⟩
  · rintro x ⟨k, hk, rfl⟩
    exact ⟨k, le_trans hnm hk, rfl⟩


theorem q8_cauchy_real_converges {u : ℕ → ℝ} (hu : CauchySeq u) :
    ∃ p : ℝ, Tendsto u atTop (nhds p) := by
  obtain ⟨R, _hRpos, hR⟩ := cauchySeq_bdd hu
  -- A Cauchy sequence is globally bounded, so each tail has a lower envelope.
  have hrangebelow : BddBelow (range u) := by
    refine ⟨u 0 - R, ?_⟩
    rintro x ⟨m, rfl⟩
    have hdist := hR 0 m
    rw [Real.dist_eq] at hdist
    nlinarith [le_abs_self (u 0 - u m)]
  -- The infimum of each tail rises as the tail is shortened.
  let v : ℕ → ℝ := tailInf u
  have hbelow : ∀ n : ℕ, BddBelow (u '' Set.Ici n) := by
    intro n
    rcases hrangebelow with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro x ⟨m, hm, rfl⟩
    exact hb ⟨m, rfl⟩
  have hnonempty : ∀ n : ℕ, (u '' Set.Ici n).Nonempty := by
    intro n
    exact ⟨u n, ⟨n, by simp, rfl⟩⟩
  have hv_mono : Monotone v := by
    simpa [v] using q7_tailInf_monotone hrangebelow
  have hv_bdd : BddAbove (range v) := by
    refine ⟨u 0 + R, ?_⟩
    rintro x ⟨n, rfl⟩
    calc
      v n ≤ u n := csInf_le (hbelow n) ⟨n, by simp, rfl⟩
      _ ≤ u 0 + R := by
        have hdist := hR 0 n
        rw [Real.dist_eq] at hdist
        nlinarith [neg_le_abs (u 0 - u n)]
  -- q4 gives a limit for these increasingly sharp lower approximations.
  have hvlim := q4_monotone_tends_to_sup hv_mono hv_bdd
  refine ⟨sSup (range v), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 hu) (ε / 2) (by linarith)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hvlim) (ε / 2) (by linarith)
  refine ⟨max N K, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnK : K ≤ n := le_trans (le_max_right _ _) hn
  have hvle : v n ≤ sSup (range v) := le_csSup hv_bdd ⟨n, rfl⟩
  have hvclose := hK n hnK
  -- Cauchy control says every later tail term lies within `ε / 2` of its first term.
  have htail : u n - ε / 2 ≤ v n := by
    apply le_csInf (hnonempty n)
    rintro x ⟨m, hm, rfl⟩
    have hdist := hN n hnN m (le_trans hnN hm)
    rw [Real.dist_eq] at hdist
    nlinarith [le_abs_self (u n - u m)]
  have hvnu : v n ≤ u n :=
    csInf_le (hbelow n) ⟨n, by simp, rfl⟩
  -- The tail infimum lies within `ε / 2` of both the chosen limit and the current tail term.
  rw [Real.dist_eq, abs_lt]
  rw [Real.dist_eq, abs_of_nonpos] at hvclose
  · constructor <;> linarith
  · exact sub_nonpos.mpr hvle


theorem q9_monotone_subsequence (u : ℕ → ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (u ∘ φ)) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Antitone (u ∘ φ) := by
  classical
  -- A peak is an index after which the sequence never rises above its current value.
  by_cases hpeaks : ∀ N : ℕ, ∃ n > N, ∀ m > n, u m ≤ u n
  · right
    -- Infinitely many peaks themselves form a nonincreasing subsequence.
    obtain ⟨φ, hφ, hpeak⟩ := Nat.exists_strictMono_subsequence hpeaks
    refine ⟨φ, hφ, ?_⟩
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact hpeak i (φ j) (hφ hij)
  · left
    push Not at hpeaks
    obtain ⟨N, hN⟩ := hpeaks
    -- Otherwise, after one index there are no peaks, so repeatedly moving to a later larger value
    -- produces a nondecreasing subsequence.
    have hnext : ∀ n : ℕ, N < n → ∃ m : ℕ, n < m ∧ u n < u m := by
      intro n hn
      exact hN n hn
    -- Once peaks stop occurring, every later index can be followed by a strictly larger value.
    let next : ℕ → ℕ := fun n => if hn : N < n then Classical.choose (hnext n hn) else n + 1
    have hnext_gt : ∀ n : ℕ, N < n → n < next n := by
      intro n hn
      simp [next, hn, (Classical.choose_spec (hnext n hn)).1]
    have hnext_value : ∀ n : ℕ, N < n → u n < u (next n) := by
      intro n hn
      simp [next, hn, (Classical.choose_spec (hnext n hn)).2]
    let φ : ℕ → ℕ := fun k => Nat.rec (N + 1) (fun _ n => next n) k
    have hφN : ∀ k : ℕ, N < φ k := by
      intro k
      induction k with
      | zero => simp [φ]
      | succ k ih =>
          exact lt_trans ih (by simpa [φ] using hnext_gt (φ k) ih)
    have hφstep : ∀ k : ℕ, φ k < φ (k + 1) := by
      intro k
      simpa [φ] using hnext_gt (φ k) (hφN k)
    have hφvalue : ∀ k : ℕ, u (φ k) < u (φ (k + 1)) := by
      intro k
      simpa [φ] using hnext_value (φ k) (hφN k)
    refine ⟨φ, strictMono_nat_of_lt_succ hφstep, ?_⟩
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step j hij ih => exact le_trans ih (le_of_lt (hφvalue j))


theorem q10_bolzano_weierstrass {u : ℕ → ℝ}
    (hbounded : ∃ M : ℝ, ∀ n : ℕ, |u n| ≤ M) :
    ∃ p : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (nhds p) := by
  obtain ⟨M, hM⟩ := hbounded
  -- q9 reduces boundedness to the monotone case, possibly after changing signs.
  rcases q9_monotone_subsequence u with ⟨φ, hφ, hmono⟩ | ⟨φ, hφ, hanti⟩
  · have hupper : BddAbove (range (u ∘ φ)) := by
      refine ⟨M, ?_⟩
      rintro x ⟨n, rfl⟩
      exact le_trans (le_abs_self _) (hM (φ n))
    exact ⟨sSup (range (u ∘ φ)), φ, hφ, q4_monotone_tends_to_sup hmono hupper⟩
  · let w : ℕ → ℝ := fun n => -(u ∘ φ) n
    -- Negating an antitone subsequence converts it to the increasing case.
    have hwmono : Monotone w := by
      intro m n hmn
      exact neg_le_neg (hanti hmn)
    have hwupper : BddAbove (range w) := by
      refine ⟨M, ?_⟩
      rintro x ⟨n, rfl⟩
      exact le_trans (neg_le_abs _) (hM (φ n))
    have hwlim := q4_monotone_tends_to_sup hwmono hwupper
    refine ⟨-sSup (range w), φ, hφ, ?_⟩
    simpa [w, Function.comp_def] using hwlim.neg


theorem q11_closed_interval_sequentially_compact {a b : ℝ} {u : ℕ → ℝ}
    (hu : ∀ n : ℕ, u n ∈ Set.Icc a b) :
    ∃ p ∈ Set.Icc a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (nhds p) := by
  have hbounded : ∃ M : ℝ, ∀ n : ℕ, |u n| ≤ M := by
    -- The larger endpoint absolute value bounds every point of the interval.
    refine ⟨max |a| |b|, ?_⟩
    intro n
    rw [abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le a) (hu n).1)
    · exact le_trans (hu n).2 (le_trans (le_abs_self b) (le_max_right _ _))
  -- Boundedness supplies a convergent subsequence; the endpoint inequalities pass to its limit.
  obtain ⟨p, φ, hφ, hlim⟩ := q10_bolzano_weierstrass hbounded
  have hp_le : p ≤ b := le_of_tendsto' hlim fun n => (hu (φ n)).2
  have hneg : Tendsto (fun n => -(u ∘ φ) n) atTop (nhds (-p)) := by
    simpa using hlim.neg
  have hneg_le : -p ≤ -a := le_of_tendsto' hneg fun n => by
    exact neg_le_neg (hu (φ n)).1
  refine ⟨p, ⟨by linarith, hp_le⟩, φ, hφ, hlim⟩

end Solutions.Analysis.RealSequences
