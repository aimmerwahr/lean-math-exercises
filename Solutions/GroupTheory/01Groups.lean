import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Opposite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Solutions.GroupTheory.Groups

variable {G : Type*} [Group G]

theorem q1_inv_unique {a b c : G} (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  -- Both `b` and `c` are right inverses of `a`; multiplying `a * b = a * c` by `a⁻¹` on the
  -- left (cancellation) forces them equal.
  have : a * b = a * c := by rw [hb, hc]
  exact mul_left_cancel this


theorem q2_inv_mul_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- The inverse of `a * b` is whatever undoes it on the right. Check that `b⁻¹ * a⁻¹` does:
  -- `(a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ = a * a⁻¹ = 1`.
  apply inv_eq_of_mul_eq_one_right
  rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul, mul_inv_cancel]


theorem q3_center_isSubgroup :
    ∃ H : Subgroup G, (↑H : Set G) = {a | ∀ g, a * g = g * a} := by
  -- Build the centre by hand: the set of elements commuting with everything. It contains `1`,
  -- and is closed under product and inverse.
  refine ⟨{ carrier := {a | ∀ g, a * g = g * a}
            one_mem' := by intro g; rw [one_mul, mul_one]
            mul_mem' := by
              intro a b ha hb g
              -- `(a*b)*g = a*(b*g) = a*(g*b) = (a*g)*b = (g*a)*b = g*(a*b)`
              rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
            inv_mem' := by
              intro a ha g
              -- from `a * g = g * a`, conjugating gives `a⁻¹ * g = g * a⁻¹`
              rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← ha, ← mul_assoc, inv_mul_cancel, one_mul] }, rfl⟩


theorem q4_orderOf_concrete : addOrderOf (3 : ZMod 12) = 4 := by
  -- The additive order is the least `n > 0` with `n • 3 = 0`. Here `4 • 3 = 12 = 0`, and no
  -- smaller positive multiple vanishes.
  rw [addOrderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hlt
  interval_cases m <;> decide


theorem q5_sq_eq_one_abelian (h : ∀ x : G, x * x = 1) : ∀ a b : G, a * b = b * a := by
  -- `x * x = 1` says every element is its own inverse. Then
  -- `a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a`.
  have key : ∀ x : G, x = x⁻¹ := fun x => eq_inv_of_mul_eq_one_left (h x)
  intro a b
  calc a * b = (a * b)⁻¹ := key (a * b)
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [← key a, ← key b]


theorem q6_union_isSubgroup_iff (H K : Subgroup G) :
    (↑H ∪ ↑K : Set G) = ↑(H ⊔ K) ↔ H ≤ K ∨ K ≤ H := by
  constructor
  · -- If the union is already a subgroup and neither contains the other, pick `h ∈ H \ K` and
    -- `k ∈ K \ H`. Their product lies in `H ⊔ K`, hence in `↑H ∪ ↑K`; but landing in either
    -- piece forces one of `h`, `k` across, a contradiction.
    intro hun
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hHK, hKH⟩ := hcon
    obtain ⟨h, hh, hhK⟩ := SetLike.not_le_iff_exists.mp hHK
    obtain ⟨k, kk, kkH⟩ := SetLike.not_le_iff_exists.mp hKH
    have hmem : h * k ∈ H ⊔ K :=
      mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right kk)
    rw [← SetLike.mem_coe, ← hun] at hmem
    rcases hmem with hmem | hmem
    · exact kkH (by simpa using mul_mem (inv_mem hh) hmem)
    · exact hhK (by simpa using mul_mem hmem (inv_mem kk))
  · -- Conversely, if say `H ≤ K` then `H ⊔ K = K` and `↑H ∪ ↑K = ↑K`, so both sides agree.
    rintro (h | h)
    · rw [sup_eq_right.mpr h, Set.union_eq_right.mpr h]
    · rw [sup_eq_left.mpr h, Set.union_eq_left.mpr h]


theorem q7_mul_sq_abelian (h : ∀ a b : G, (a * b) * (a * b) = (a * a) * (b * b)) :
    ∀ a b : G, a * b = b * a := by
  -- Expand `(ab)(ab) = (aa)(bb)`, then cancel `a` on the left and `b` on the right.
  intro a b
  have h1 := h a b
  rw [mul_assoc a b (a * b), mul_assoc a a (b * b)] at h1
  have h2 := mul_left_cancel h1
  rw [← mul_assoc, ← mul_assoc] at h2
  exact (mul_right_cancel h2).symm


theorem q8_even_order_involution [Fintype G] [DecidableEq G]
    (h : 2 ∣ Fintype.card G) : ∃ x : G, x ≠ 1 ∧ x * x = 1 := by
  -- Inversion `x ↦ x⁻¹` is an involution of `G`; its fixed points are exactly the solutions of
  -- `x⁻¹ = x`. The number of fixed points of an involution has the same parity as `|G|`, which
  -- is even, so the fixed-point set (which contains `1`) has an even size, hence at least two
  -- elements — giving a nonidentity `x` with `x⁻¹ = x`, i.e. `x * x = 1`.
  let f : Function.End G := fun x => x⁻¹
  have hf : f ^ (2 ^ 1) = 1 := by
    show f ^ 2 = 1
    rw [pow_two]
    show f ∘ f = id
    funext x; simp [f]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := G) (f := f) (p := 2) (n := 1) hf
  have hmem : ∀ x : G, x ∈ f.fixedPoints ↔ x⁻¹ = x := fun x => Iff.rfl
  have hdvd : 2 ∣ Fintype.card f.fixedPoints := by
    have h0 : Fintype.card G ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr h
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans h0)
  have h1mem : (1 : G) ∈ f.fixedPoints := by rw [hmem]; simp
  have hpos : 0 < Fintype.card f.fixedPoints := Fintype.card_pos_iff.mpr ⟨⟨1, h1mem⟩⟩
  have hle : 2 ≤ Fintype.card f.fixedPoints := Nat.le_of_dvd hpos hdvd
  obtain ⟨b, hb⟩ :=
    Fintype.exists_ne_of_one_lt_card (lt_of_lt_of_le one_lt_two hle) (⟨1, h1mem⟩ : f.fixedPoints)
  refine ⟨b.1, ?_, ?_⟩
  · intro hb1; exact hb (Subtype.ext hb1)
  · have hbx : b.1⁻¹ = b.1 := (hmem b.1).mp b.2
    exact mul_eq_one_iff_eq_inv.mpr hbx.symm


theorem q9_perm_noncommute : ∃ σ τ : Equiv.Perm (Fin 3), σ * τ ≠ τ * σ :=
  -- Two overlapping transpositions do not commute.
  ⟨Equiv.swap 0 1, Equiv.swap 0 2, by decide⟩


theorem q10_q8_noncommutative :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0
      ≠ QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  -- In `Q₈`, `i * j = k` but `j * i = -k`; the two products differ.
  decide


theorem q11_q8_not_iso_d4 : IsEmpty (QuaternionGroup 2 ≃* DihedralGroup 4) := by
  -- An isomorphism preserves the solution set of `x * x = 1`. But that equation has `2`
  -- solutions in `Q₈` (namely `±1`) and `6` in `D₄` (the four reflections together with `1`
  -- and the half-turn), so no isomorphism can exist.
  rw [isEmpty_iff]
  intro e
  have hcard : Fintype.card {x : QuaternionGroup 2 // x * x = 1}
      = Fintype.card {y : DihedralGroup 4 // y * y = 1} :=
    Fintype.card_congr
      { toFun := fun x => ⟨e x, by rw [← map_mul, x.2, map_one]⟩
        invFun := fun y => ⟨e.symm y, by rw [← map_mul, y.2, map_one]⟩
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
  have h2 : Fintype.card {x : QuaternionGroup 2 // x * x = 1} = 2 := by decide
  have h6 : Fintype.card {y : DihedralGroup 4 // y * y = 1} = 6 := by decide
  rw [h2, h6] at hcard
  exact absurd hcard (by decide)


theorem q12_opposite_iso :
    ∃ e : G ≃* Gᵐᵒᵖ, ∀ x, e x = MulOpposite.op x⁻¹ := by
  -- Sending `x` to `x⁻¹` in the opposite group is an isomorphism: reversing the product exactly
  -- compensates for `(x*y)⁻¹ = y⁻¹ * x⁻¹`.
  refine ⟨{ toFun := fun x => MulOpposite.op x⁻¹
            invFun := fun y => (MulOpposite.unop y)⁻¹
            left_inv := fun x => by simp
            right_inv := fun y => by simp
            map_mul' := fun x y => by simp [mul_inv_rev] }, fun x => rfl⟩


theorem q13_subgroup_inter_glb {ι : Type*} (H : ι → Subgroup G) :
    ∃ K : Subgroup G, (∀ i, K ≤ H i) ∧ (∀ L : Subgroup G, (∀ i, L ≤ H i) → L ≤ K) := by
  -- The intersection `⋂ᵢ Hᵢ`, built directly as a subgroup, is below every `Hᵢ`, and swallows
  -- any subgroup that is below every `Hᵢ` — that is exactly the greatest-lower-bound property.
  refine ⟨{ carrier := {x | ∀ i, x ∈ H i}
            one_mem' := fun i => (H i).one_mem
            mul_mem' := fun ha hb i => (H i).mul_mem (ha i) (hb i)
            inv_mem' := fun ha i => (H i).inv_mem (ha i) }, ?_, ?_⟩
  · intro i x hx; exact hx i
  · intro L hL x hx i; exact hL i hx

end Solutions.GroupTheory.Groups
