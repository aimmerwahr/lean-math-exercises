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

theorem q6_int_prime_maximal (p : ℕ) [Fact p.Prime] : (Ideal.span ({p : ℤ})).IsMaximal := by
  -- Quotienting the integers by a prime leaves the field `ZMod p`.
  infer_instance

theorem q7_int_prime_ideal (p : ℕ) [Fact p.Prime] : (Ideal.span ({p : ℤ})).IsPrime := by
  exact q6_int_prime_maximal p |>.isPrime

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
