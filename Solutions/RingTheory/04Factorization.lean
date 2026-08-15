import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

namespace Solutions.RingTheory.Factorization

open scoped Polynomial

theorem q1_polynomial_bezout :
    27 * (Polynomial.X ^ 3 + 2 * Polynomial.X ^ 2 - 4 * Polynomial.X + 6 : ℤ[X]) +
      (-9 * Polynomial.X ^ 2 - 12 * Polynomial.X + 44) * (3 * Polynomial.X + 2) = 250 := by
  ring

private theorem x5_small_degree :
    (Polynomial.C 4 * Polynomial.X - Polynomial.C 2 : ℤ[X]).degree < 5 := by
  calc
    (Polynomial.C 4 * Polynomial.X - Polynomial.C 2 : ℤ[X]).degree ≤
        max (Polynomial.C 4 * Polynomial.X : ℤ[X]).degree (Polynomial.C 2 : ℤ[X]).degree :=
      Polynomial.degree_sub_le _ _
    _ ≤ 1 := by
      rw [Polynomial.degree_mul, Polynomial.degree_C (by norm_num : (4 : ℤ) ≠ 0),
        Polynomial.degree_C (by norm_num : (2 : ℤ) ≠ 0), Polynomial.degree_X]
      norm_num
    _ < 5 := by norm_num

private theorem x5_monic :
    (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]).Monic :=
  Polynomial.monic_X_pow_sub x5_small_degree

private theorem x5_natDegree :
    (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]).natDegree = 5 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_sub_eq_left_of_degree_lt]
  · simp
  · simpa using x5_small_degree

theorem q2_eisenstein_x5_sub_fourX_add_two :
    Irreducible (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) := by
  let f : ℤ[X] := Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2)
  let P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hf : f.Monic := by simpa [f] using x5_monic
  have hdeg : f.natDegree = 5 := by simpa [f] using x5_natDegree
  have hP : P.IsPrime := by
    rw [show P = Ideal.span ({(2 : ℤ)} : Set ℤ) by rfl, Ideal.span_singleton_prime]
    · exact Int.prime_two
    · norm_num
  have he : f.IsEisensteinAt P := hf.isEisensteinAt_of_mem_of_notMem hP.ne_top (by
    intro n hn
    rw [hdeg] at hn
    interval_cases n <;> simp [f, P, Ideal.mem_span_singleton, Polynomial.coeff_X]) (by
    rw [show P ^ 2 = Ideal.span ({(2 : ℤ)} : Set ℤ) ^ 2 by rfl, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    norm_num [f])
  exact he.irreducible hP hf.isPrimitive (by rw [hdeg]; norm_num)

private theorem cubic_small_degree :
    (Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X + Polynomial.C 12 : ℤ[X]).degree < 3 := by
  calc
    _ ≤ max (max (Polynomial.C 6 * Polynomial.X ^ 2 : ℤ[X]).degree
        (Polynomial.C 9 * Polynomial.X : ℤ[X]).degree) (Polynomial.C 12 : ℤ[X]).degree :=
      (Polynomial.degree_add_le _ _).trans (max_le_max (Polynomial.degree_add_le _ _) le_rfl)
    _ ≤ 2 := by
      rw [Polynomial.degree_mul, Polynomial.degree_C (by norm_num : (6 : ℤ) ≠ 0), Polynomial.degree_X_pow,
        Polynomial.degree_mul, Polynomial.degree_C (by norm_num : (9 : ℤ) ≠ 0), Polynomial.degree_X,
        Polynomial.degree_C (by norm_num : (12 : ℤ) ≠ 0)]
      norm_num
    _ < 3 := by norm_num

theorem q3_eisenstein_cubic :
    Irreducible (Polynomial.X ^ 3 +
      (Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X + Polynomial.C 12) : ℤ[X]) := by
  let f : ℤ[X] := Polynomial.X ^ 3 +
    (Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X + Polynomial.C 12)
  let P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hf : f.Monic := by
    dsimp [f]
    exact Polynomial.monic_X_pow_add cubic_small_degree
  have hdeg : f.natDegree = 3 := by
    dsimp [f]
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · simp
    · simpa using cubic_small_degree
  have hP : P.IsPrime := by
    rw [show P = Ideal.span ({(3 : ℤ)} : Set ℤ) by rfl, Ideal.span_singleton_prime]
    · exact Int.prime_three
    · norm_num
  have he : f.IsEisensteinAt P := hf.isEisensteinAt_of_mem_of_notMem hP.ne_top (by
    intro n hn
    rw [hdeg] at hn
    interval_cases n <;> simp [f, P, Ideal.mem_span_singleton, Polynomial.coeff_X]) (by
    rw [show P ^ 2 = Ideal.span ({(3 : ℤ)} : Set ℤ) ^ 2 by rfl, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    norm_num [f])
  exact he.irreducible hP hf.isPrimitive (by rw [hdeg]; norm_num)

theorem q4_prime_divides_a_factor (g h : ℤ[X]) :
    (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) ∣ g * h →
      (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) ∣ g ∨
        (Polynomial.X ^ 5 - (Polynomial.C 4 * Polynomial.X - Polynomial.C 2) : ℤ[X]) ∣ h := by
  exact (irreducible_iff_prime.mp q2_eisenstein_x5_sub_fourX_add_two).dvd_mul.mp

private theorem zsqrt5_norm_ge_two_of_nonunit {z : ℤ√(-5)} (hz : z ≠ 0) (hu : ¬ IsUnit z) :
    2 ≤ z.norm := by
  have hnonneg : 0 ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z
  have hpos : 0 < z.norm := lt_of_le_of_ne hnonneg
    (Ne.symm ((Zsqrtd.norm_eq_zero_iff (by norm_num) z).not.mpr hz))
  have hne : z.norm ≠ 1 := fun h => hu ((Zsqrtd.norm_eq_one_iff' (by norm_num) z).mp h)
  omega

private theorem irreducible_of_norm_four {z : ℤ√(-5)} (hz : z.norm = 4)
    (hno2 : ∀ w : ℤ√(-5), w.norm ≠ 2) : Irreducible z := by
  rw [irreducible_iff]
  constructor
  · intro hu
    have : z.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) z).mpr hu
    omega
  · intro a b hab
    by_contra h
    push_neg at h
    have hz0 : z ≠ 0 := by intro hz0; rw [hz0, Zsqrtd.norm_zero] at hz; norm_num at hz
    have ha0 : a ≠ 0 := by intro ha; subst a; simp at hab; exact hz0 hab
    have hb0 : b ≠ 0 := by intro hb; subst b; simp at hab; exact hz0 hab
    have hna := zsqrt5_norm_ge_two_of_nonunit ha0 h.1
    have hnb := zsqrt5_norm_ge_two_of_nonunit hb0 h.2
    have hprod : a.norm * b.norm = 4 := by rw [← Zsqrtd.norm_mul, ← hab, hz]
    have hale : a.norm ≤ 2 := by nlinarith
    have ha : a.norm = 2 := by omega
    exact hno2 a ha

theorem q5_zsqrt5_two_factorizations :
    let s : ℤ√(-5) := ⟨0, 1⟩
    let α : ℤ√(-5) := 1 + s
    let β : ℤ√(-5) := 1 - s
    (6 : ℤ√(-5)) = (2 : ℤ√(-5)) * 3 ∧
      (6 : ℤ√(-5)) = α * β ∧
      (2 : ℤ√(-5)).norm = 4 ∧ (3 : ℤ√(-5)).norm = 9 ∧
      α.norm = 6 ∧ β.norm = 6 ∧
      (∀ z : ℤ√(-5), z.norm ≠ 2) ∧ (∀ z : ℤ√(-5), z.norm ≠ 3) := by
  dsimp
  refine ⟨by norm_num, by ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul], by norm_num [Zsqrtd.norm],
    by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm], by norm_num [Zsqrtd.norm], ?_, ?_⟩
  · intro z h
    rw [Zsqrtd.norm_def] at h
    have him : z.im * z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him0 : z.im = 0 := by exact mul_self_eq_zero.mp him
    rw [him0] at h
    have hlo : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re + 1)]
    have hhi : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re - 1)]
    interval_cases z.re <;> norm_num at h
  · intro z h
    rw [Zsqrtd.norm_def] at h
    have him : z.im * z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him0 : z.im = 0 := by exact mul_self_eq_zero.mp him
    rw [him0] at h
    have hlo : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re + 1)]
    have hhi : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re - 1)]
    interval_cases z.re <;> norm_num at h

end Solutions.RingTheory.Factorization
