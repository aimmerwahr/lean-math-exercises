import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic
import Exercises.RingTheory.«01Rings»

namespace Solutions.RingTheory.Rings

variable {R : Type*} [CommRing R]

open Exercises.RingTheory.Rings
open Exercises.RingTheory.Rings.Hamilton

theorem q1_neg_mul (a b : R) : (-a) * b = -(a * b) := by
  exact neg_mul a b

theorem q2_unit_not_zero_divisor {a b : R} (ha : IsUnit a) (hab : a * b = 0) : b = 0 := by
  rcases ha with ⟨u, rfl⟩
  -- Multiplying by the inverse of a unit cancels its nonzero factor.
  have h := congrArg (fun x : R => (↑(u⁻¹) : R) * x) hab
  simpa [mul_assoc] using h

theorem q3_char_prime_or_zero (p : ℕ) [IsDomain R] [CharP R p] : p.Prime ∨ p = 0 := by
  -- If `p = mk`, then the product of the casts of `m` and `k` is zero.  In a domain one factor
  -- must vanish, so the minimality encoded by the characteristic makes the factorization trivial.
  by_cases hp0 : p = 0
  · exact Or.inr hp0
  left
  rw [Nat.prime_def]
  refine ⟨?_, ?_⟩
  · have hp1 : p ≠ 1 := by
      intro hp1
      have hone : (1 : R) = 0 := by
        rw [← Nat.cast_one, ← hp1]
        exact CharP.cast_eq_zero R p
      exact one_ne_zero hone
    omega
  · intro m hmp
    rcases hmp with ⟨k, hk⟩
    have hmp : m ∣ p := ⟨k, hk⟩
    have hcast : (m : R) * (k : R) = 0 := by
      rw [← Nat.cast_mul, ← hk]
      exact CharP.cast_eq_zero R p
    rcases mul_eq_zero.mp hcast with hm0 | hk0
    · right
      exact Nat.dvd_antisymm hmp (CharP.cast_eq_zero_iff R p m |>.mp hm0)
    · left
      have hpdk : p ∣ k := CharP.cast_eq_zero_iff R p k |>.mp hk0
      have hkpos : 0 < k := by
        by_contra hkpos
        have hkzero : k = 0 := by omega
        exact hp0 (hk.trans (by simp [hkzero]))
      have hpkle : p ≤ k := Nat.le_of_dvd hkpos hpdk
      have hmkle : m * k ≤ k := by simpa [← hk] using hpkle
      have hmle : m ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using hmkle) hkpos
      have hmpos : 0 < m := by
        by_contra hmpos
        have hmzero : m = 0 := by omega
        exact hp0 (hk.trans (by simp [hmzero]))
      omega

theorem q4_zmod12_unit : IsUnit (5 : ZMod 12) := by
  -- The residue 5 is coprime to 12, so multiplication by it is reversible modulo 12.
  exact ZMod.isUnit_iff_coprime 5 12 |>.mpr (by decide)

theorem q5_int_initial (f : ℤ →+* R) : f = Int.castRingHom R := by
  -- A ring map must preserve both `1` and repeated addition, so its value on every integer is fixed.
  exact RingHom.ext_int f (Int.castRingHom R)

theorem q6_finite_domain_units [Finite R] [IsDomain R] {a : R} (ha : a ≠ 0) : IsUnit a := by
  -- Multiplication by `a` is injective: equal products differ by a product `a(x-y)` equal to zero.
  -- On a finite set it is therefore surjective, so some `b` satisfies `ab = 1`.
  rw [isUnit_iff_exists]
  have hinj : Function.Injective (fun x : R => a * x) := by
    intro x y hxy
    change a * x = a * y at hxy
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left ha
    rw [mul_sub, hxy, sub_self]
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj 1
  change a * b = 1 at hb
  refine ⟨b, hb, ?_⟩
  rw [mul_comm, hb]

theorem q7_zmod12_two_zero_divisor :
    ¬ IsUnit (2 : ZMod 12) ∧ (2 : ZMod 12) * 6 = 0 ∧ (6 : ZMod 12) ≠ 0 := by
  constructor
  · -- A common factor with the modulus prevents a residue from being invertible.
    change ¬ IsUnit ((2 : ℕ) : ZMod 12)
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  constructor
  · change ((12 : ℕ) : ZMod 12) = 0
    rw [ZMod.natCast_eq_zero_iff]
  · change ((6 : ℕ) : ZMod 12) ≠ 0
    intro h
    have hdiv : 12 ∣ 6 := (ZMod.natCast_eq_zero_iff 6 12).mp h
    norm_num at hdiv

theorem q8_zmod12_unit_iff (a : ZMod 12) :
    IsUnit a ↔ ∃ n : ℕ, a = n ∧ n.Coprime 12 := by
  constructor
  · intro ha
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
    exact ⟨n, rfl, ZMod.isUnit_iff_coprime n 12 |>.mp ha⟩
  · rintro ⟨n, rfl, hn⟩
    exact ZMod.isUnit_iff_coprime n 12 |>.mpr hn

theorem q9_boolean_two_torsion_and_comm {S : Type*} [Ring S]
    (h : ∀ x : S, x * x = x) (a b : S) : a + a = 0 ∧ a * b = b * a := by
  -- First expand `(x+x)² = x+x`: it leaves `2x = 0` for every `x`.
  have htwo (x : S) : x + x = 0 := by
    have hfour : (x + x) + (x + x) = x + x := by
      calc
        (x + x) + (x + x) = (x + x) * (x + x) := by
          rw [mul_add, add_mul, h x]
        _ = x + x := h (x + x)
    apply add_left_cancel (a := x + x)
    simpa using hfour
  constructor
  · exact htwo a
  · -- Expanding `(a+b)² = a+b` gives `ab + ba = 0`; since `2ba = 0`, this forces `ab = ba`.
    have hab := h (a + b)
    have hcross : a * b + b * a = 0 := by
      have hexpand : (a * a + b * a) + (a * b + b * b) = a + b := by
        simpa only [mul_add, add_mul] using hab
      have hdiagonal : (a + b * a) + (a * b + b) = a + b := by
        simpa only [h a, h b] using hexpand
      apply add_left_cancel (a := a + b)
      calc
        (a + b) + (a * b + b * a) = (a + b * a) + (a * b + b) := by abel
        _ = a + b := hdiagonal
        _ = (a + b) + 0 := (add_zero _).symm
    calc
      a * b = a * b + 0 := (add_zero _).symm
      _ = a * b + (b * a + b * a) := by rw [htwo (b * a)]
      _ = (a * b + b * a) + b * a := by abel
      _ = b * a := by rw [hcross, zero_add]

theorem q10_gaussian_no_zero_divisors (z w : GaussianInt) (hzw : z * w = 0) : z = 0 ∨ w = 0 := by
  -- Norms multiply.  Since an integer product is zero only when one factor is zero, one of the
  -- two Gaussian norms vanishes, and hence one of the two Gaussian integers vanishes.
  have hnorm : z.norm * w.norm = 0 := by
    rw [← Zsqrtd.norm_mul, hzw]
    rfl
  exact (Int.mul_eq_zero.mp hnorm).imp GaussianInt.norm_eq_zero.mp GaussianInt.norm_eq_zero.mp

private theorem hamilton_normSq_ne_zero (q : Hamilton) (hq : q ≠ zero) : normSq q ≠ 0 := by
  rintro h
  rcases q with ⟨a, b, c, d⟩
  dsimp [normSq] at h
  have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc2 : c ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
  have hd2 : d ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have ha : a = 0 := sq_eq_zero_iff.mp ha2
  have hb : b = 0 := sq_eq_zero_iff.mp hb2
  have hc : c = 0 := sq_eq_zero_iff.mp hc2
  have hd : d = 0 := sq_eq_zero_iff.mp hd2
  apply hq
  simp [zero, ha, hb, hc, hd]

private theorem hamilton_mul_inv (q : Hamilton) (hq : q ≠ zero) : mul q (inv q) = one := by
  rcases q with ⟨a, b, c, d⟩
  have hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≠ 0 := by
    simpa [normSq] using hamilton_normSq_ne_zero ⟨a, b, c, d⟩ hq
  ext <;> dsimp [mul, inv, scale, conj, normSq, one, zero] at *
  all_goals
    field_simp [hnorm]
    ring

private theorem hamilton_inv_mul (q : Hamilton) (hq : q ≠ zero) : mul (inv q) q = one := by
  rcases q with ⟨a, b, c, d⟩
  have hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≠ 0 := by
    simpa [normSq] using hamilton_normSq_ne_zero ⟨a, b, c, d⟩ hq
  ext <;> dsimp [mul, inv, scale, conj, normSq, one, zero] at *
  all_goals
    field_simp [hnorm]
    ring

theorem q11_hamilton_inverse_and_noncommutative (q : Hamilton) (hq : q ≠ zero) :
    (∃ r, mul q r = one ∧ mul r q = one) ∧ mul qi qj = neg (mul qj qi) := by
  -- Conjugation reverses the imaginary coordinates, and division by the positive squared norm
  -- makes it a two-sided inverse.  The coordinate multiplication also gives `ij = -ji`.
  refine ⟨⟨inv q, hamilton_mul_inv q hq, hamilton_inv_mul q hq⟩, ?_⟩
  simp [mul, qi, qj, neg]

theorem q12_int_scalar_action_unique {A : Type*} [AddCommGroup A] (act : ℤ → A → A)
    (hact : IsIntScalarAction act) (n : ℤ) (a : A) : act n a = n • a := by
  -- Starting at zero, add one to reach positive integers and subtract one to reach negative
  -- integers.  Additivity forces exactly the usual repeated-addition rule in both directions.
  rcases hact with ⟨hzero, hone, hadd⟩
  induction n using Int.induction_on with
  | zero => simpa using hzero a
  | succ n ih =>
      rw [show (n + 1 : ℤ) = n + 1 by omega, hadd, ih, hone]
      simp [add_zsmul]
  | pred n ih =>
      have hsum := hadd (-↑n - 1) 1 a
      rw [show (-↑n - 1 : ℤ) + 1 = -↑n by omega, ih, hone] at hsum
      calc
        act (-↑n - 1) a = (-↑n : ℤ) • a - a := eq_sub_iff_add_eq.mpr hsum.symm
        _ = (-↑n - 1 : ℤ) • a := by rw [sub_eq_add_neg, sub_zsmul]; simp

private theorem zmod_prime_iff_cast_no_zero_divisors (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a b : ℕ, (a : ZMod n) * b = 0 → (a : ZMod n) = 0 ∨ (b : ZMod n) = 0 := by
  constructor
  · intro hp a b hab
    rw [← Nat.cast_mul] at hab
    have hdivides : n ∣ a * b := (ZMod.natCast_eq_zero_iff (a * b) n).mp hab
    rcases hp.dvd_mul.mp hdivides with ha | hb
    · exact Or.inl ((ZMod.natCast_eq_zero_iff a n).mpr ha)
    · exact Or.inr ((ZMod.natCast_eq_zero_iff b n).mpr hb)
  · intro h
    have hnpos : 0 < n := by omega
    rw [Nat.prime_def_lt]
    refine ⟨hn, ?_⟩
    intro m hm hmn
    rcases hmn with ⟨k, hk⟩
    have hproduct : (m : ZMod n) * k = 0 := by
      rw [← Nat.cast_mul, ← hk]
      exact ZMod.natCast_self n
    rcases h m k hproduct with hmzero | hkzero
    · have hnm : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp hmzero
      have hmpos : 0 < m := by
        by_contra hmpos
        have hmzero : m = 0 := by omega
        simp [hmzero] at hk
        omega
      have hnle : n ≤ m := Nat.le_of_dvd hmpos hnm
      omega
    · have hnk : n ∣ k := (ZMod.natCast_eq_zero_iff k n).mp hkzero
      have hkpos : 0 < k := by
        by_contra hkpos
        have hkzero : k = 0 := by omega
        simp [hkzero] at hk
        omega
      have hnle : n ≤ k := Nat.le_of_dvd hkpos hnk
      have hmkle : m * k ≤ k := by simpa [← hk] using hnle
      have hmle : m ≤ 1 := Nat.le_of_mul_le_mul_right (by simpa using hmkle) hkpos
      have hmpos : 0 < m := by
        by_contra hmpos
        have hmzero : m = 0 := by omega
        simp [hmzero] at hk
        omega
      omega

theorem q13_zmod_no_zero_divisors_iff_prime (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ∀ a b : ZMod n, a * b = 0 → a = 0 ∨ b = 0 := by
  constructor
  · intro hp a b hab
    letI : NeZero n := ⟨Nat.ne_of_gt (by omega)⟩
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective b
    -- Every residue has a natural representative, so primality reduces the product to a
    -- divisibility statement in the natural numbers.
    exact zmod_prime_iff_cast_no_zero_divisors n hn |>.mp hp m k hab
  · intro h
    apply zmod_prime_iff_cast_no_zero_divisors n hn |>.mpr
    intro a b hab
    exact h a b hab

theorem q14_gaussian_units_exactly_four (z : GaussianInt) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ := by
  constructor
  · intro hz
    rw [isUnit_iff_exists] at hz
    obtain ⟨w, hzw, _⟩ := hz
    -- A unit has an inverse, so its nonnegative norm divides one and must itself be one.
    have hnorm : z.norm = 1 := by
      apply Int.eq_one_of_dvd_one (Zsqrtd.norm_nonneg (by norm_num) z)
      refine ⟨w.norm, ?_⟩
      rw [← Zsqrtd.norm_mul, hzw, Zsqrtd.norm_one]
    have hsum : z.re * z.re + z.im * z.im = 1 := by
      simpa [Zsqrtd.norm_def] using hnorm
    -- Each coordinate has absolute value at most one.  The norm equation leaves exactly four
    -- lattice points on this circle.
    have hrelower : -1 ≤ z.re := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have hreupper : z.re ≤ 1 := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have himlower : -1 ≤ z.im := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have himupper : z.im ≤ 1 := by nlinarith [Int.sq_nonneg z.re, Int.sq_nonneg z.im]
    have hrecases : z.re = -1 ∨ z.re = 0 ∨ z.re = 1 := by omega
    have himcases : z.im = -1 ∨ z.im = 0 ∨ z.im = 1 := by omega
    rcases hrecases with hre | hre | hre <;> rcases himcases with him | him | him
    all_goals simp [hre, him, Zsqrtd.ext_iff] at hsum ⊢
  · rintro (rfl | rfl | rfl | rfl)
    -- The four displayed elements come in inverse pairs.
    all_goals rw [isUnit_iff_exists]
    · exact ⟨1, one_mul _, mul_one _⟩
    · exact ⟨-1, by ring, by ring⟩
    · exact ⟨⟨0, -1⟩, by ext <;> norm_num, by ext <;> norm_num⟩
    · exact ⟨⟨0, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩

end Solutions.RingTheory.Rings
