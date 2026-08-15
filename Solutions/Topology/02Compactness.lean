import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Solutions.Topology.Compactness

open Set Filter Uniformity
open _root_.Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem q1_finite_compact {Z : Type*} [TopologicalSpace Z] {s : Set Z} (hs : s.Finite) :
    IsCompact s := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact isCompact_empty
  | insert x hxs hs_compact =>
      -- Compactness is preserved when one point is adjoined, so induction builds every finite set.
      rw [Set.insert_eq]
      exact isCompact_singleton.union hs_compact


theorem q2_closed_interval_compact (a b : ℝ) : IsCompact (Set.Icc a b) := by
  -- In the real line, closedness and boundedness supply the finite-subcover property.
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_Icc, Metric.isBounded_Icc a b⟩


theorem q3_compact_image {K : Set X} (hK : IsCompact K) {f : X → Y}
    (hf : ContinuousOn f K) : IsCompact (f '' K) := by
  rw [isCompact_iff_finite_subcover]
  intro ι U hU hcover
  -- Pull each open member of the image cover back to an open set around `K`.
  choose V hVopen hV_eq using fun i => continuousOn_iff'.mp hf (U i) (hU i)
  have hVcover : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨i, hfx⟩ := Set.mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
    have hxV : x ∈ f ⁻¹' U i ∩ K := ⟨hfx, hx⟩
    rw [hV_eq i] at hxV
    exact Set.mem_iUnion.mpr ⟨i, hxV.1⟩
  obtain ⟨t, htcover⟩ := hK.elim_finite_subcover V hVopen hVcover
  refine ⟨t, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, hit, hxV⟩ := Set.mem_iUnion₂.mp (htcover hx)
  refine Set.mem_iUnion₂.mpr ⟨i, hit, ?_⟩
  have hxV' : x ∈ V i ∩ K := ⟨hxV, hx⟩
  rw [← hV_eq i] at hxV'
  exact hxV'.1


theorem q4_extreme_value {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f y ≤ f x) ∧
      ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x ≤ f y := by
  have hinterval := q2_closed_interval_compact a b
  have himage := q3_compact_image hinterval hf
  have hdomain_nonempty : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  -- The compact image has a largest and a smallest value; pull their witnesses back to the
  -- original interval.
  constructor
  · obtain ⟨z, hz_image, hz_max⟩ := himage.exists_isGreatest (hdomain_nonempty.image f)
    obtain ⟨x, hx, hfx⟩ := hz_image
    refine ⟨x, hx, ?_⟩
    intro y hy
    calc
      f y ≤ z := hz_max ⟨y, hy, rfl⟩
      _ = f x := hfx.symm
  · obtain ⟨z, hz_image, hz_min⟩ := himage.exists_isLeast (hdomain_nonempty.image f)
    obtain ⟨x, hx, hfx⟩ := hz_image
    refine ⟨x, hx, ?_⟩
    intro y hy
    calc
      f x = z := hfx
      _ ≤ f y := hz_min ⟨y, hy, rfl⟩


theorem q5_uniform_continuity_compact {K : Set X} (hK : IsCompact K) {f : X → Y}
    (hf : ContinuousOn f K) : UniformContinuousOn f K := by
  rw [uniformContinuousOn_iff_restrict]
  rw [continuousOn_iff_continuous_restrict] at hf
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K → Y := Set.restrict K f
  have hg : Continuous g := hf
  -- Compactness identifies the uniform structure with neighborhoods of the diagonal; continuity
  -- therefore controls every pair of sufficiently close points at once.
  calc
    map (Prod.map g g) (𝓤 K) =
        map (Prod.map g g) (𝓝ˢ (diagonal K)) := by
          rw [nhdsSet_diagonal_eq_uniformity]
    _ ≤ 𝓝ˢ (diagonal Y) := (hg.prodMap hg).tendsto_nhdsSet mapsTo_prodMap_diagonal
    _ ≤ 𝓤 Y := nhdsSet_diagonal_le_uniformity


theorem q6_real_compact_neighborhood {x : ℝ} {U : Set ℝ} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r > 0, IsCompact (Set.Icc (x - r) (x + r)) ∧ Set.Icc (x - r) (x + r) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  -- Shrink an open ball around `x` to a closed interval of half its radius.
  refine ⟨ε / 2, half_pos hε, q2_closed_interval_compact _ _, ?_⟩
  intro y hy
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have hy_bound : |y - x| ≤ ε / 2 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  exact lt_of_le_of_lt hy_bound (by linarith)

end Solutions.Topology.Compactness
