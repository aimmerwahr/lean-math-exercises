import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Solutions.Topology.Connectedness

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem q1_indiscrete_connected [Nonempty X] [IndiscreteTopology X] :
    IsConnected (Set.univ : Set X) := by
  refine ⟨univ_nonempty, ?_⟩
  -- Each open set is either empty or the whole space, so an open cover by two of them cannot
  -- separate two points of the space.
  intro u v hu hv huv hu' hv'
  rw [IndiscreteTopology.isOpen_iff] at hu hv
  rcases hu with rfl | rfl <;> simp_all


theorem q2_continuous_image_connected {s : Set X} (hs : IsConnected s) (f : X → Y)
    (hf : ContinuousOn f s) : IsConnected (f '' s) := by
  refine ⟨image_nonempty.mpr hs.nonempty, ?_⟩
  -- Pull a proposed separation of the image back to open sets around the original set.
  rintro u v hu hv huv ⟨_, ⟨x, hxs, rfl⟩, hxu⟩ ⟨_, ⟨y, hys, rfl⟩, hyv⟩
  rcases continuousOn_iff'.mp hf u hu with ⟨u', hu', hu'_eq⟩
  rcases continuousOn_iff'.mp hf v hv with ⟨v', hv', hv'_eq⟩
  have hcover : s ⊆ u' ∪ v' := by
    rw [image_subset_iff, preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [union_inter_distrib_right, hu'_eq, hv'_eq, ← union_inter_distrib_right] at huv
    exact (subset_inter_iff.mp huv).1
  -- The connected original set has a point lying in both pulled-back pieces.
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).Nonempty := by
    refine hs.isPreconnected u' v' hu' hv' hcover ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [hu'_eq ▸ ⟨hxu, hxs⟩, hv'_eq ▸ ⟨hyv, hys⟩]
  -- Its image lies in both pieces of the proposed separation.
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc, inter_comm s, inter_comm s,
    ← hu'_eq, ← hv'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩


theorem q3_connected_product {s : Set X} {t : Set Y} (hs : IsConnected s) (ht : IsConnected t) :
    IsConnected (s ×ˢ t) := by
  refine ⟨hs.nonempty.prod ht.nonempty, ?_⟩
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  -- Join the two points by a vertical slice and a horizontal slice meeting at `(a₁, b₂)`.
  refine ⟨Prod.mk a₁ '' t ∪ flip Prod.mk b₂ '' s, ?_, .inl ⟨b₁, hb₁, rfl⟩,
    .inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨ha₁, hy⟩
    · exact ⟨hx, hb₂⟩
  -- The slices are connected copies of the factors and have the displayed common point.
  exact (ht.isPreconnected.image _ (by fun_prop)).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.isPreconnected.image _ (Continuous.prodMk_left _).continuousOn)


theorem q4_quotient_connected {q : X → Y} (hq : Topology.IsQuotientMap q)
    (hX : IsConnected (Set.univ : Set X)) : IsConnected (Set.univ : Set Y) := by
  -- A quotient map is continuous, so Question 2 connects its image. Surjectivity says that
  -- this image is all of the quotient.
  have himage : IsConnected (q '' (Set.univ : Set X)) :=
    q2_continuous_image_connected hX q hq.isCoinducing.continuous.continuousOn
  have hrange : Set.range q = Set.univ := Set.range_eq_univ.mpr hq.surjective
  simpa only [image_univ, hrange] using himage


theorem q5_union_intervals_connected {a b c d : ℝ}
    (hcommon : (Set.Icc a b ∩ Set.Icc c d).Nonempty) :
    (Set.Icc a b ∪ Set.Icc c d).OrdConnected ∧ IsConnected (Set.Icc a b ∪ Set.Icc c d) := by
  rcases hcommon with ⟨x, hx₁, hx₂⟩
  constructor
  · rw [Set.ordConnected_iff]
    intro p hp q hq _hpq r hr
    -- If the endpoints come from different intervals, the common point tells us which interval
    -- contains the intermediate point.
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · left
      exact ⟨hp.1.trans hr.1, hr.2.trans hq.2⟩
    · by_cases hrb : r ≤ b
      · left
        exact ⟨hp.1.trans hr.1, hrb⟩
      · right
        exact ⟨hx₂.1.trans (hx₁.2.trans (le_of_lt (lt_of_not_ge hrb))), hr.2.trans hq.2⟩
    · by_cases hrd : r ≤ d
      · right
        exact ⟨hp.1.trans hr.1, hrd⟩
      · left
        exact ⟨hx₁.1.trans (hx₂.2.trans (le_of_lt (lt_of_not_ge hrd))), hr.2.trans hq.2⟩
    · right
      exact ⟨hp.1.trans hr.1, hr.2.trans hq.2⟩
  · refine ⟨⟨x, Or.inl hx₁⟩, ?_⟩
    -- Two preconnected sets that meet cannot be separated after they are united.
    exact isPreconnected_Icc.union x hx₁ hx₂ isPreconnected_Icc


theorem q6_punctured_interval_disconnected :
    ¬ IsConnected (Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1) := by
  intro hconnected
  have hcover : Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1 ⊆ Set.Iio 0 ∪ Set.Ioi 0 := by
    rintro w (hw | hw)
    · exact Or.inl hw.2
    · exact Or.inr hw.1
  have hleft : (-1 / 2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1 := by
    left
    norm_num
  have hright : (1 / 2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo 0 1 := by
    right
    norm_num
  obtain ⟨w, _, hwlt, hwgt⟩ :=
    hconnected.isPreconnected (Set.Iio 0) (Set.Ioi 0) isOpen_Iio isOpen_Ioi hcover
      ⟨-1 / 2, hleft, by norm_num⟩ ⟨1 / 2, hright, by norm_num⟩
  -- A separating point would have to lie on both strict sides of zero.
  change w < 0 at hwlt
  change 0 < w at hwgt
  exact (lt_asymm hwlt hwgt)


theorem q7_connected_real_is_interval {s : Set ℝ} (hs : IsConnected s) : s.OrdConnected := by
  rw [Set.ordConnected_iff]
  intro x hx y hy _hxy z hz
  by_contra hzs
  -- A missing point between two points of the set puts those points on opposite strict sides.
  have hxz : x < z := lt_of_le_of_ne hz.1 fun hxz => hzs (hxz ▸ hx)
  have hzy : z < y := lt_of_le_of_ne hz.2 fun hzy => hzs (hzy ▸ hy)
  have hcover : s ⊆ Set.Iio z ∪ Set.Ioi z := by
    intro w hw
    rcases lt_trichotomy w z with hwz | rfl | hzw
    · exact Or.inl hwz
    · exact False.elim (hzs hw)
    · exact Or.inr hzw
  obtain ⟨w, _, hwlt, hwgt⟩ :=
    hs.isPreconnected (Set.Iio z) (Set.Ioi z) isOpen_Iio isOpen_Ioi hcover
      ⟨x, hx, hxz⟩ ⟨y, hy, hzy⟩
  -- A point cannot lie strictly on both sides of the missing real number.
  change w < z at hwlt
  change z < w at hwgt
  exact (lt_asymm hwlt hwgt)


theorem q8_intermediate_value {a b u : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hu : u ∈ Set.Icc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = u := by
  -- The domain interval is connected, hence so is its image under the continuous function.
  have hdomain : IsConnected (Set.Icc a b) :=
    ⟨⟨a, le_rfl, hab⟩, isPreconnected_Icc⟩
  have himage := q2_continuous_image_connected hdomain f hf
  have hleft : f a ∈ f '' Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hright : f b ∈ f '' Set.Icc a b := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  -- Question 7 says the connected image includes everything between its endpoint values.
  obtain ⟨c, hc, hfc⟩ := (q7_connected_real_is_interval himage).out hleft hright hu
  exact ⟨c, hc, hfc⟩


theorem q9_sign_change_zero {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  -- Zero lies between the endpoint values, so Question 8 supplies the required point.
  exact q8_intermediate_value hab hf ⟨le_of_lt hfa, le_of_lt hfb⟩

end Solutions.Topology.Connectedness
