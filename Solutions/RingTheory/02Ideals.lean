import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Tactic

namespace Solutions.RingTheory.Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem q1_ideals_of_int (I : Ideal ℤ) : ∃ n : ℤ, I = Ideal.span {n} := by
  -- The integers are a principal ideal ring, so one generator suffices for every ideal.
  obtain ⟨n, hn⟩ := IsPrincipalIdealRing.principal I
  exact ⟨n, hn⟩


theorem q2_first_iso_ring (f : R →+* S) : Nonempty (R ⧸ f.ker ≃+* f.range) := by
  -- Quotienting removes exactly the information that the homomorphism loses.
  exact ⟨f.quotientKerEquivRange⟩


theorem q3_quotient_domain_iff_prime (I : Ideal R) : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  exact Ideal.Quotient.isDomain_iff_isPrime


theorem q4_maximal_prime (I : Ideal R) (hI : I.IsMaximal) : I.IsPrime := by
  -- A proper enlargement of a maximal ideal can only be the whole ring.
  exact hI.isPrime


theorem q5_crt_ring (m n : ℕ) (h : m.Coprime n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) := by
  -- Coprime congruence conditions may be imposed independently.
  exact ⟨ZMod.chineseRemainder h⟩


theorem q6_int_prime_maximal (p : ℕ) [Fact p.Prime] :
    Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊤ ∧
    ∀ J : Ideal ℤ, Ideal.span ({(p : ℤ)} : Set ℤ) < J → J = ⊤ := by
  have hp : p.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · -- p ≥ 2 is not a unit in ℤ; the ideal is proper.
    rw [Ideal.span_singleton_eq_top, Int.isUnit_iff, Int.natAbs_ofNat]
    exact hp.one_lt.ne'
  · intro J hJ
    -- Witness the strict containment: find x ∈ J with p ∤ x.
    obtain ⟨x, hxJ, hxnp⟩ := Set.not_subset.mp (not_le.mpr hJ)
    simp only [Ideal.mem_coe, Ideal.mem_span_singleton] at hxnp
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
      (J.mul_mem_left _ (Ideal.mem_coe.mp hxJ))


theorem q7_int_prime_ideal (p : ℕ) [Fact p.Prime] : (Ideal.span ({p : ℤ})).IsPrime := by
  obtain ⟨hne, hmax⟩ := q6_int_prime_maximal p
  exact (show (Ideal.span ({p : ℤ})).IsMaximal from ⟨hne, hmax⟩).isPrime


theorem q8_zero_ideal_prime : (⊥ : Ideal ℤ).IsPrime := by
  exact Ideal.isPrime_bot


theorem q9_kernel_constant_coeff :
    RingHom.ker (Polynomial.constantCoeff : R[X] →+* R) = Ideal.span {Polynomial.X} := by
  exact Polynomial.ker_constantCoeff


theorem q10_map_nilpotent (f : R →+* S) (x : R) (n : ℕ) (hx : x ^ n = 0) :
    (f x) ^ n = 0 := by
  simpa using congrArg f hx


theorem q11_two_X_mem_span :
    (2 : ℤ[X]) ∈ Ideal.span ({(2 : ℤ[X]), Polynomial.X} : Set ℤ[X]) ∧
      Polynomial.X ∈ Ideal.span ({(2 : ℤ[X]), Polynomial.X} : Set ℤ[X]) := by
  constructor <;> exact Ideal.subset_span (by simp)

end Solutions.RingTheory.Ideals
