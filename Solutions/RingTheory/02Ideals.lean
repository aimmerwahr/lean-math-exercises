import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Tactic

namespace Solutions.RingTheory.Ideals

open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

theorem q1_ideals_of_int (I : Ideal ℤ) : ∃ n : ℤ, I = Ideal.span {n} := by
  -- The integers are a principal ideal ring, so one generator suffices for every ideal.
  obtain ⟨n, hn⟩ := IsPrincipalIdealRing.principal I
  exact ⟨n, hn⟩


theorem q2_first_iso_ring (f : R →+* S) : Nonempty (R ⧸ RingHom.ker f ≃+* f.range) := by
  -- First descend `f` to the quotient: elements of its kernel become zero there.
  let g : R ⧸ RingHom.ker f →+* f.range :=
    Ideal.Quotient.lift (RingHom.ker f) f.rangeRestrict (by
      intro x hx
      exact Subtype.ext hx)
  -- No further identifications remain after quotienting by the kernel, and every point in the
  -- range still has a preimage.
  have hg_injective : Function.Injective g := by
    dsimp [g]
    exact RingHom.lift_injective_of_ker_le_ideal (RingHom.ker f) (f := f.rangeRestrict)
      (fun x hx => Subtype.ext hx) (RingHom.ker_rangeRestrict f).le
  have hg_surjective : Function.Surjective g := by
    apply Ideal.Quotient.lift_surjective_of_surjective
    exact f.rangeRestrict_surjective
  exact ⟨RingEquiv.ofBijective g ⟨hg_injective, hg_surjective⟩⟩


theorem q3_quotient_domain_iff_prime (I : Ideal R) : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  constructor
  · intro hdomain
    refine ⟨?_, ?_⟩
    · intro htop
      -- If `I = ⊤`, then the quotient has `0 = 1`, contradicting that it is a domain.
      letI : Nontrivial (R ⧸ I) := hdomain.toNontrivial
      have hone : Ideal.Quotient.mk I (1 : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (htop.symm ▸ Submodule.mem_top)
      have honezero : (1 : R ⧸ I) = 0 := by simpa only [map_one] using hone
      exact (one_ne_zero : (1 : R ⧸ I) ≠ 0) honezero
    · intro x y hxy
      -- A zero product in the quotient is exactly a product lying in `I`.
      have hzero : Ideal.Quotient.mk I x * Ideal.Quotient.mk I y = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact hxy
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with hx | hy
      · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.mp hx)
      · exact Or.inr (Ideal.Quotient.eq_zero_iff_mem.mp hy)
  · intro hprime
    -- Conversely, primality makes a zero product of residue classes force one factor to vanish.
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hprime.1
    letI : NoZeroDivisors (R ⧸ I) :=
      { eq_zero_or_eq_zero_of_mul_eq_zero := by
          intro a b hab
          refine Quotient.inductionOn₂' a b ?_ hab
          intro x y hxy
          exact (hprime.mem_or_mem (Ideal.Quotient.eq_zero_iff_mem.mp hxy)).elim
            (Or.inl ∘ Ideal.Quotient.eq_zero_iff_mem.mpr)
            (Or.inr ∘ Ideal.Quotient.eq_zero_iff_mem.mpr) }
    exact NoZeroDivisors.to_isDomain _


theorem q4_quotient_field_iff_maximal (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I) := by
  constructor
  · intro hmax
    -- A maximal ideal makes every nonzero residue class invertible.
    letI : I.IsMaximal := hmax
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    exact Ideal.Quotient.exists_inv ha
  · intro hfield
    -- Conversely, a proper ideal strictly containing `I` would make a nonzero residue class
    -- invertible, forcing `1` into that larger ideal.
    apply Ideal.isMaximal_iff.2
    constructor
    · intro htop
      rcases hfield.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
      exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ htop))
    · intro J x hIJ hxnI hxJ
      rcases hfield.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩
      rw [← zero_add (1 : R), ← sub_self (x * y), sub_add]
      exact J.sub_mem (J.mul_mem_right _ hxJ) (hIJ (Ideal.Quotient.eq.1 hy))


theorem q5_maximal_prime (I : Ideal R) (hI : I.IsMaximal) : I.IsPrime := by
  -- A maximal ideal has a field quotient; a field has no zero divisors.
  apply (q3_quotient_domain_iff_prime I).mp
  exact ((q4_quotient_field_iff_maximal I).mp hI).isDomain


theorem q6_crt_ring (m n : ℕ) (h : m.Coprime n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) := by
  -- Coprime congruence conditions may be imposed independently.
  exact ⟨ZMod.chineseRemainder h⟩


theorem q7_int_prime_maximal (p : ℕ) [Fact p.Prime] :
    Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊤ ∧
    ∀ J : Ideal ℤ, Ideal.span ({(p : ℤ)} : Set ℤ) < J → J = ⊤ := by
  have hp : p.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · -- p ≥ 2 is not a unit in ℤ; the ideal is proper.
    intro htop
    have hunit : IsUnit (p : ℤ) := Ideal.span_singleton_eq_top.mp htop
    exact hp.ne_one (by simpa [Int.isUnit_iff] using hunit)
  · intro J hJ
    -- Witness the strict containment: find x ∈ J with p ∤ x.
    have hnot : ¬ J ≤ Ideal.span ({(p : ℤ)} : Set ℤ) := not_le_of_gt hJ
    obtain ⟨x, hxJ, hxnp⟩ := SetLike.not_le_iff_exists.mp hnot
    rw [Ideal.mem_span_singleton] at hxnp
    -- gcd(p, x) divides p; primality forces gcd = 1 or gcd = p.
    have hgcd1 : Int.gcd (p : ℤ) x = 1 := by
      rcases hp.eq_one_or_self_of_dvd (Int.gcd (p : ℤ) x)
          (by exact_mod_cast Int.gcd_dvd_left (p : ℤ) x) with h | h
      · exact h
      -- gcd = p would mean p ∣ x, contradicting hxnp.
      · exact absurd (h ▸ (by exact_mod_cast Int.gcd_dvd_right (p : ℤ) x)) hxnp
    -- Bezout: gcdA·p + gcdB·x = 1; both terms lie in J, so 1 ∈ J.
    rw [Ideal.eq_top_iff_one]
    have hbez : Int.gcdA (p : ℤ) x * p + Int.gcdB (p : ℤ) x * x = 1 := by
      have h := Int.gcd_eq_gcd_ab (p : ℤ) x
      rw [show (Int.gcd (p : ℤ) x : ℤ) = 1 from by exact_mod_cast hgcd1] at h
      linarith [mul_comm (p : ℤ) (Int.gcdA (p : ℤ) x),
                mul_comm x (Int.gcdB (p : ℤ) x)]
    rw [← hbez]
    exact J.add_mem
      (J.mul_mem_left _ (hJ.le (Ideal.mem_span_singleton_self _)))
      (J.mul_mem_left _ hxJ)


theorem q8_zero_prime_not_maximal : (⊥ : Ideal ℤ).IsPrime ∧ ¬ (⊥ : Ideal ℤ).IsMaximal := by
  constructor
  · refine ⟨?_, ?_⟩
    · exact bot_ne_top
    · intro x y hxy
      rw [Submodule.mem_bot] at hxy ⊢
      exact eq_zero_or_eq_zero_of_mul_eq_zero hxy
  · intro hmax
    -- The nontrivial ideal `(2)` sits strictly between `(0)` and the whole ring.
    have hproper : (⊥ : Ideal ℤ) < Ideal.span ({(2 : ℤ)} : Set ℤ) := by
      refine lt_of_le_of_ne bot_le ?_
      intro h
      have htwo : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := by
        rw [h]
        exact Ideal.mem_span_singleton_self 2
      norm_num [Submodule.mem_bot] at htwo
    have hnot_top : Ideal.span ({(2 : ℤ)} : Set ℤ) ≠ ⊤ := by
      intro htop
      have hunit : IsUnit (2 : ℤ) := Ideal.span_singleton_eq_top.mp htop
      norm_num [Int.isUnit_iff] at hunit
    exact hnot_top (hmax.1.2 _ hproper)


theorem q9_kernel_constant_coeff :
    RingHom.ker (Polynomial.constantCoeff : R[X] →+* R) = Ideal.span {Polynomial.X} := by
  -- Having zero constant coefficient is exactly divisibility by `X`, which is membership in `(X)`.
  ext p
  simp only [RingHom.mem_ker, Polynomial.constantCoeff_apply, ← Polynomial.X_dvd_iff,
    Ideal.mem_span_singleton]


theorem q10_map_nilpotent (f : R →+* S) (x : R) (n : ℕ) (hx : x ^ n = 0) :
    (f x) ^ n = 0 := by
  simpa using congrArg f hx


theorem q11_two_X_mem_span :
    (2 : ℤ[X]) ∈ Ideal.span ({(2 : ℤ[X]), Polynomial.X} : Set ℤ[X]) ∧
      Polynomial.X ∈ Ideal.span ({(2 : ℤ[X]), Polynomial.X} : Set ℤ[X]) := by
  constructor <;> exact Ideal.subset_span (by simp)

end Solutions.RingTheory.Ideals
