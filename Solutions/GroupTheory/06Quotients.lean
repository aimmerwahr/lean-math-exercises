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
  -- Kernels are conjugation-stable, and the quotient projection identifies exactly the elements of N.
  exact ⟨MonoidHom.normal_ker f, QuotientGroup.ker_mk' N⟩

theorem q5_third_iso (N M : Subgroup G) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ Subgroup.map (QuotientGroup.mk' N) M ≃* G ⧸ M) := by
  -- The two-stage quotient remembers precisely the same cosets as quotienting directly by M.
  exact ⟨QuotientGroup.quotientQuotientEquivQuotient N M hNM⟩

theorem q6_abelianization {A : Type*} [CommGroup A] (f : G →* A) :
    ∃ F : Abelianization G →* A, ∀ g : G, F (Abelianization.of g) = f g := by
  -- Commutators vanish in every abelian target, so f descends uniquely to the abelianization.
  exact ⟨Abelianization.lift f, fun _ => rfl⟩

theorem q7_quotient_concrete :
    Nonempty (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3) ≃*
      (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ).range) := by
  -- The even permutations are exactly those of sign +1, so first isomorphism applies to sign.
  exact ⟨MulEquiv.ofBijective (QuotientGroup.rangeKerLift Equiv.Perm.sign)
    ⟨QuotientGroup.rangeKerLift_injective Equiv.Perm.sign,
      QuotientGroup.rangeKerLift_surjective Equiv.Perm.sign⟩⟩

theorem q8_quotient_trivial : Nonempty (G ⧸ (⊥ : Subgroup G) ≃* G) ∧
    Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  -- Modding out by only the identity changes nothing; modding out by every element leaves one coset.
  exact ⟨⟨QuotientGroup.quotientBot⟩, QuotientGroup.subsingleton_quotient_top⟩

theorem q9_quotient_center_cyclic_abelian [IsCyclic (G ⧸ Subgroup.center G)] (a b : G) :
    a * b = b * a := by
  -- A cyclic quotient by the center has only one noncentral direction, which forces commutation.
  exact (isMulCommutative_of_isCyclic_quotient_center_self G).is_comm.comm a b

def firstFactor (A B : Type*) [Group A] [Group B] : A →* A × B where
  toFun := fun a => (a, 1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

def secondProjection (A B : Type*) [Group A] [Group B] : A × B →* B where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl

theorem q10_short_exact_sequence (A B : Type*) [Group A] [Group B] :
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
