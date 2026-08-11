import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

namespace Solutions.GroupTheory.Quotients

variable {G H : Type*} [Group G] [Group H]

theorem q1_normal_iff_conjugates (N : Subgroup G) :
    N.Normal ↔ ∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N := by
  constructor
  · intro h; exact h.conj_mem
  · intro h; exact ⟨h⟩


theorem q2_index_two_normal (N : Subgroup G) (hindex : N.index = 2) : N.Normal := by
  constructor
  intro n hn g
  -- With only two cosets, multiplying by a member preserves membership on either side.
  rw [N.mul_mem_iff_of_index_two hindex]
  constructor
  · intro hgn
    have hg : g ∈ N := (N.mul_mem_iff_of_index_two hindex).mp hgn |>.mpr hn
    exact inv_mem hg
  · intro hginv
    have hg : g ∈ N := by simpa using (inv_mem hginv)
    exact (N.mul_mem_iff_of_index_two hindex).mpr ⟨fun _ => hn, fun _ => hg⟩


theorem q3_first_iso (f : G →* H) : Nonempty (G ⧸ f.ker ≃* f.range) := by
  -- The induced map from the quotient has no remaining kernel and reaches every image element.
  exact ⟨MulEquiv.ofBijective (QuotientGroup.rangeKerLift f)
    ⟨QuotientGroup.rangeKerLift_injective f, QuotientGroup.rangeKerLift_surjective f⟩⟩


theorem q4_normal_iff_kernel (f : G →* H) (N : Subgroup G) [N.Normal] :
    f.ker.Normal ∧ (QuotientGroup.mk' N).ker = N := by
  constructor
  · constructor
    intro x hx g
    rw [MonoidHom.mem_ker] at hx ⊢
    simp [f.map_mul, f.map_inv, hx]
  · ext x
    change (x : G ⧸ N) = 1 ↔ x ∈ N
    rw [QuotientGroup.eq_one_iff]


set_option backward.isDefEq.respectTransparency false in
theorem q5_third_iso (N M : Subgroup G) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ Subgroup.map (QuotientGroup.mk' N) M ≃* G ⧸ M) := by
  -- The map is induced by the projection `G / N → G / M`; construct its inverse as well.
  refine ⟨MonoidHom.toMulEquiv
    (QuotientGroup.quotientQuotientEquivQuotientAux N M hNM)
    (QuotientGroup.map M (Subgroup.map (QuotientGroup.mk' N) M) (QuotientGroup.mk' N)
      (Subgroup.le_comap_map _ _)) ?_ ?_⟩
  · ext x
    simp
  · ext x
    simp


theorem q6_commutator_le_ker {A : Type*} [CommGroup A] (f : G →* A) :
    commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]


theorem q7_abelianization {A : Type*} [CommGroup A] (f : G →* A) :
    ∃ F : Abelianization G →* A, ∀ g : G, F (Abelianization.of g) = f g := by
  refine ⟨QuotientGroup.lift (commutator G) f (q6_commutator_le_ker f), ?_⟩
  intro g
  rfl


theorem q8_quotient_concrete :
    Nonempty (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3) ≃*
      (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).range) := by
  -- The even permutations are exactly those of sign +1, so first isomorphism applies to sign.
  exact ⟨MulEquiv.ofBijective (QuotientGroup.rangeKerLift Equiv.Perm.sign)
    ⟨QuotientGroup.rangeKerLift_injective Equiv.Perm.sign,
      QuotientGroup.rangeKerLift_surjective Equiv.Perm.sign⟩⟩


theorem q9_quotient_trivial : Nonempty (G ⧸ (⊥ : Subgroup G) ≃* G) ∧
    Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  let descend : G ⧸ (⊥ : Subgroup G) →* G :=
    QuotientGroup.lift ⊥ (MonoidHom.id G) (by
      intro x hx
      simpa using hx)
  constructor
  · refine ⟨MonoidHom.toMulEquiv descend (QuotientGroup.mk' ⊥) ?_ ?_⟩
    · ext x
      rfl
    · ext x
      rfl
  · constructor
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    change (x : G ⧸ (⊤ : Subgroup G)) = y
    rw [QuotientGroup.eq_iff_div_mem]
    trivial


theorem q10_quotient_center_cyclic_abelian [IsCyclic (G ⧸ Subgroup.center G)] (a b : G) :
    a * b = b * a := by
  let f : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  have hker : f.ker ≤ Subgroup.center G := by
    intro x hx
    change (x : G ⧸ Subgroup.center G) = 1 at hx
    rw [QuotientGroup.eq_one_iff] at hx
    exact hx
  obtain ⟨⟨x, y, hxy⟩, hx⟩ := IsCyclic.exists_generator (α := f.range)
  obtain ⟨m, hm⟩ := hx ⟨f a, a, rfl⟩
  obtain ⟨n, hn⟩ := hx ⟨f b, b, rfl⟩
  have hm : x ^ m = f a := by simpa [Subtype.ext_iff] using hm
  have hn : x ^ n = f b := by simpa [Subtype.ext_iff] using hn
  have ha : y ^ (-m) * a ∈ Subgroup.center G :=
    hker (by
      rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x m, hm, inv_mul_cancel])
  have hb : y ^ (-n) * b ∈ Subgroup.center G :=
    hker (by
      rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x n, hn, inv_mul_cancel])
  calc
    a * b = y ^ m * (y ^ (-m) * a * y ^ n) * (y ^ (-n) * b) := by simp [mul_assoc]
    _ = y ^ m * (y ^ n * (y ^ (-m) * a)) * (y ^ (-n) * b) := by
      rw [Subgroup.mem_center_iff.mp ha]
    _ = y ^ m * y ^ n * y ^ (-m) * (a * (y ^ (-n) * b)) := by simp [mul_assoc]
    _ = y ^ m * y ^ n * y ^ (-m) * (y ^ (-n) * b * a) := by
      rw [Subgroup.mem_center_iff.mp hb]
    _ = b * a := by group

def firstFactor (A B : Type*) [Group A] [Group B] : A →* A × B where
  toFun := fun a => (a, 1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

def secondProjection (A B : Type*) [Group A] [Group B] : A × B →* B where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl


theorem q11_short_exact_sequence (A B : Type*) [Group A] [Group B] :
    Function.Injective (firstFactor A B) ∧ Function.Surjective (secondProjection A B) ∧
      (firstFactor A B).range = (secondProjection A B).ker := by
  constructor
  · intro a b hab
    -- Looking at the first coordinate recovers an element of A from its embedded pair.
    change (a, 1) = (b, 1) at hab
    exact congrArg Prod.fst hab
  constructor
  · intro b
    -- Every element of B is the second coordinate of `(1, b)`.
    exact ⟨(1, b), rfl⟩
  · ext x
    constructor
    · rintro ⟨a, ha⟩
      -- Pairs in the first-factor image have second coordinate equal to the identity.
      rw [MonoidHom.mem_ker]
      simpa [firstFactor, secondProjection] using (congrArg Prod.snd ha).symm
    · intro hx
      -- Conversely, a pair with trivial second coordinate came from its first coordinate.
      rw [MonoidHom.mem_ker] at hx
      refine ⟨x.1, ?_⟩
      cases x
      simpa [firstFactor, secondProjection] using hx.symm

end Solutions.GroupTheory.Quotients
