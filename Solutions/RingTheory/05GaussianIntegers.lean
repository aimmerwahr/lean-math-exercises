import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic
import Solutions.RingTheory.«01Rings»

namespace Solutions.RingTheory.GaussianIntegers

open scoped GaussianInt


def i : GaussianInt := ⟨0, 1⟩


private theorem norm_product_direct (z w : GaussianInt) :
    z * star z = (z.norm : GaussianInt) ∧ (z * w).norm = z.norm * w.norm := by
  constructor
  · ext <;> simp [Zsqrtd.norm, Zsqrtd.re_mul, Zsqrtd.im_mul] ; ring
  · simp [Zsqrtd.norm, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring


theorem q1_conjugate_norm_product (z w : GaussianInt) :
    z * star z = (z.norm : GaussianInt) ∧ (z * w).norm = z.norm * w.norm ∧
      (1 + i).norm = 2 ∧ (2 + i).norm = 5 ∧ (3 + 2 * i).norm = 13 := by
  refine ⟨(norm_product_direct z w).1, (norm_product_direct z w).2, ?_, ?_, ?_⟩ <;>
    norm_num [i, Zsqrtd.norm]


private theorem norm_one_unit (z : GaussianInt) (hz : z.norm = 1) : IsUnit z := by
  apply isUnit_iff_dvd_one.mpr
  refine ⟨star z, ?_⟩
  rw [show z * star z = (z.norm : GaussianInt) from (norm_product_direct z z).1, hz]
  rfl


theorem q2_norm_prime_irreducible (p : ℕ) (hp : p.Prime) (z : GaussianInt)
    (hz : z.norm = p) : Irreducible z := by
  rw [irreducible_iff]
  constructor
  · intro hu
    rcases isUnit_iff_dvd_one.mp hu with ⟨w, hw⟩
    have hprod : z.norm * w.norm = 1 := by
      rw [← (norm_product_direct z w).2, ← hw]
      norm_num [Zsqrtd.norm]
    have hnz : 0 ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z
    rw [hz] at hprod hnz
    have hdiv : (p : ℤ) ∣ 1 := ⟨w.norm, hprod.symm⟩
    have hpone : (p : ℤ) = 1 := Int.eq_one_of_dvd_one hnz hdiv
    have hptwo : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    omega
  · intro a b hab
    have hprod : a.norm * b.norm = p := by rw [← (norm_product_direct a b).2, ← hab, hz]
    have hna : 0 ≤ a.norm := Zsqrtd.norm_nonneg (by norm_num) a
    have hnb : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by norm_num) b
    have habs : a.norm.natAbs * b.norm.natAbs = p := by
      rw [← Int.natAbs_mul]
      simpa using congrArg Int.natAbs hprod
    have hdiv : a.norm.natAbs ∣ p := ⟨b.norm.natAbs, habs.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdiv with ha | ha
    · left
      apply norm_one_unit a
      rw [← Int.natAbs_of_nonneg hna, ha]
      norm_num
    · right
      apply norm_one_unit b
      have hb : b.norm.natAbs = 1 := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        simpa [ha] using habs
      rw [← Int.natAbs_of_nonneg hnb, hb]
      norm_num


private theorem not_unit_of_norm_ne_one {z : GaussianInt} (hz : z.norm ≠ 1) : ¬ IsUnit z := by
  intro hu
  rcases isUnit_iff_dvd_one.mp hu with ⟨w, hw⟩
  have hprod : z.norm * w.norm = 1 := by
    rw [← (norm_product_direct z w).2, ← hw]
    norm_num [Zsqrtd.norm]
  exact hz <| Int.eq_one_of_dvd_one (Zsqrtd.norm_nonneg (by norm_num) z) ⟨w.norm, hprod.symm⟩


theorem q3_two_ramifies :
    (2 : GaussianInt) = -i * (1 + i) ^ 2 ∧ Irreducible (1 + i) ∧ ¬ Irreducible (2 : GaussianInt) := by
  refine ⟨?_, q2_norm_prime_irreducible 2 Nat.prime_two _ (by norm_num [i, Zsqrtd.norm]), ?_⟩
  ext <;> norm_num [i, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  intro h
  rcases h.2 (show (2 : GaussianInt) = (1 + i) * (1 - i) by ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]) with hu | hu
  · exact not_unit_of_norm_ne_one (by norm_num [i, Zsqrtd.norm]) hu
  · exact not_unit_of_norm_ne_one (by norm_num [i, Zsqrtd.norm]) hu


private theorem five_not_associated : ¬ Associated (2 + i) (2 - i) := by
  rintro ⟨u, hu⟩
  rcases (Solutions.RingTheory.Rings.q14_gaussian_units_exactly_four (u : GaussianInt)).mp u.isUnit with h | h | h | h
  all_goals rw [h] at hu
  all_goals have hre := congrArg Zsqrtd.re hu
  all_goals have him := congrArg Zsqrtd.im hu
  all_goals norm_num [i, Zsqrtd.re_mul] at hre
  all_goals norm_num [i, Zsqrtd.im_mul] at him


private theorem thirteen_not_associated : ¬ Associated (3 + 2 * i) (3 - 2 * i) := by
  rintro ⟨u, hu⟩
  rcases (Solutions.RingTheory.Rings.q14_gaussian_units_exactly_four (u : GaussianInt)).mp u.isUnit with h | h | h | h
  all_goals rw [h] at hu
  all_goals have hre := congrArg Zsqrtd.re hu
  all_goals have him := congrArg Zsqrtd.im hu
  all_goals norm_num [i, Zsqrtd.re_mul] at hre
  all_goals norm_num [i, Zsqrtd.im_mul] at him


theorem q4_five_splits :
    (5 : GaussianInt) = (2 + i) * (2 - i) ∧ Irreducible (2 + i) ∧ Irreducible (2 - i) ∧
      ¬ Associated (2 + i) (2 - i) := by
  refine ⟨?_, q2_norm_prime_irreducible 5 (by norm_num) _ (by norm_num [i, Zsqrtd.norm]),
    q2_norm_prime_irreducible 5 (by norm_num) _ (by norm_num [i, Zsqrtd.norm]), five_not_associated⟩
  ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]


theorem q5_thirteen_splits :
    (13 : GaussianInt) = (3 + 2 * i) * (3 - 2 * i) ∧
      Irreducible (3 + 2 * i) ∧ Irreducible (3 - 2 * i) ∧ ¬ Associated (3 + 2 * i) (3 - 2 * i) := by
  refine ⟨?_, q2_norm_prime_irreducible 13 (by norm_num) _ (by norm_num [i, Zsqrtd.norm]),
    q2_norm_prime_irreducible 13 (by norm_num) _ (by norm_num [i, Zsqrtd.norm]), thirteen_not_associated⟩
  ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]


theorem q6_euclidean_algorithm :
    (3 - i : GaussianInt) = (-1 - i) * (2 * i) + (1 + i) ∧
      (2 * i : GaussianInt) = (1 + i) * (1 + i) ∧ (1 + i).norm < (2 * i).norm ∧
      (1 + i : GaussianInt) ∣ 3 - i ∧ (1 + i : GaussianInt) ∣ 2 * i := by
  refine ⟨?_, ?_, by norm_num [i, Zsqrtd.norm], ?_, ?_⟩
  · ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · refine ⟨1 - 2 * i, ?_⟩
    ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · refine ⟨1 + i, ?_⟩
    ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]


theorem q7_bezout_and_principal_ideal :
    (1 + i : GaussianInt) = (3 - i) + (1 + i) * (2 * i) ∧
      Ideal.span ({(3 - i : GaussianInt), 2 * i} : Set GaussianInt) = Ideal.span ({1 + i} : Set GaussianInt) := by
  have hbez : (1 + i : GaussianInt) = (3 - i) + (1 + i) * (2 * i) := by
    ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
  refine ⟨hbez, ?_⟩
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro x (rfl | rfl)
    · apply Ideal.mem_span_singleton.mpr
      refine ⟨1 - 2 * i, ?_⟩
      ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
    · apply Ideal.mem_span_singleton.mpr
      refine ⟨1 + i, ?_⟩
      ext <;> norm_num [i, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · rw [Ideal.span_le]
    rintro x rfl
    have h₁ : (3 - i : GaussianInt) ∈ Ideal.span ({(3 - i : GaussianInt), 2 * i} : Set GaussianInt) :=
      Ideal.subset_span (by simp)
    have h₂ : (2 * i : GaussianInt) ∈ Ideal.span ({(3 - i : GaussianInt), 2 * i} : Set GaussianInt) :=
      Ideal.subset_span (by simp)
    rw [hbez]
    exact (Ideal.span ({(3 - i : GaussianInt), 2 * i} : Set GaussianInt)).add_mem h₁
      ((Ideal.span ({(3 - i : GaussianInt), 2 * i} : Set GaussianInt)).mul_mem_left _ h₂)


private theorem no_norm_three : ∀ z : GaussianInt, z.norm ≠ 3 := by
  intro z h
  rw [Zsqrtd.norm_def] at h
  have hrelo : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re + 2), sq_nonneg z.im]
  have hrehi : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re - 2), sq_nonneg z.im]
  have himlo : -1 ≤ z.im := by nlinarith [sq_nonneg (z.im + 2), sq_nonneg z.re]
  have himhi : z.im ≤ 1 := by nlinarith [sq_nonneg (z.im - 2), sq_nonneg z.re]
  interval_cases z.re <;> interval_cases z.im <;> norm_num at h


theorem q8_three_is_irreducible_and_prime :
    (∀ z : GaussianInt, z.norm ≠ 3) ∧ Irreducible (3 : GaussianInt) ∧ Prime (3 : GaussianInt) := by
  have hirr : Irreducible (3 : GaussianInt) := by
    rw [irreducible_iff]
    constructor
    · exact not_unit_of_norm_ne_one (by norm_num [Zsqrtd.norm])
    · intro a b hab
      by_contra h
      push Not at h
      have ha0 : a ≠ 0 := by intro ha; subst a; norm_num at hab
      have hb0 : b ≠ 0 := by intro hb; subst b; norm_num at hab
      have hpa : 0 < a.norm := lt_of_le_of_ne (Zsqrtd.norm_nonneg (by norm_num) a)
        (Ne.symm ((Zsqrtd.norm_eq_zero_iff (by norm_num) a).not.mpr ha0))
      have hpb : 0 < b.norm := lt_of_le_of_ne (Zsqrtd.norm_nonneg (by norm_num) b)
        (Ne.symm ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).not.mpr hb0))
      have hna : 2 ≤ a.norm := by
        have hne : a.norm ≠ 1 := fun e => h.1 (norm_one_unit a e)
        omega
      have hnb : 2 ≤ b.norm := by
        have hne : b.norm ≠ 1 := fun e => h.2 (norm_one_unit b e)
        omega
      have hprod : a.norm * b.norm = 9 := by
        rw [← (norm_product_direct a b).2, ← hab]
        norm_num [Zsqrtd.norm]
      have hale : a.norm ≤ 4 := by nlinarith
      have hcases : a.norm = 2 ∨ a.norm = 3 ∨ a.norm = 4 := by omega
      rcases hcases with ha | ha | ha
      · rw [ha] at hprod
        omega
      · have hb : b.norm = 3 := by nlinarith
        exact no_norm_three b hb
      · rw [ha] at hprod
        omega
  exact ⟨no_norm_three, hirr, irreducible_iff_prime.mp hirr⟩


end Solutions.RingTheory.GaussianIntegers
