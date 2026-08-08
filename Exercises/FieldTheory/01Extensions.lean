import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Tactic

/-! # Exercises — FieldTheory / Extensions and Degree -/

namespace Exercises.FieldTheory.Extensions

open scoped IntermediateField Polynomial

/-! ## Potentially helpful results -/
section

#check Complex.ext
#check Submodule.subset_span
#check Submodule.smul_mem

end

/-- **Question 1.** Every complex number has unique real and imaginary coordinates: prove that
each `z : ℂ` can be written in exactly one way as `a + b * i` with `a, b : ℝ`. -/
theorem q1_complex_coordinates (z : ℂ) :
    ∃! ab : ℝ × ℝ, z = (ab.1 : ℂ) + ab.2 * Complex.I := by sorry


/-- **Question 2.** A simple integral extension has degree the degree of its minimal polynomial. -/
theorem q2_adjoin_degree {K L : Type*} [Field K] [Field L] [Algebra K L]
    (a : L) (ha : IsIntegral K a) :
    Module.finrank K K⟮a⟯ = (minpoly K a).natDegree := by sorry


/-- **Question 3.** Degrees multiply in a finite tower. -/
theorem q3_tower_law {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [FiniteDimensional K F] [FiniteDimensional F L] :
    Module.finrank K F * Module.finrank F L = Module.finrank K L := by sorry


/-- **Question 4.** Every element of a finite extension is algebraic. -/
theorem q4_finite_implies_algebraic {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : L) : IsAlgebraic K a := by sorry


/-- **Question 5.** A scalar from the base field has minimal polynomial `X - C a`. -/
theorem q5_minpoly_base (K : Type*) [Field K] (a : K) :
    minpoly K a = Polynomial.X - Polynomial.C a := by sorry


theorem q6_intermediate_degree_dvd {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (F : IntermediateField K L) :
    Module.finrank K F ∣ Module.finrank K L := by sorry


theorem q7_sqrt2_irrational : Irrational (Real.sqrt 2) := by sorry


/-- **Question 8.** The base field is generated over itself by the single element `1`. -/
theorem q8_base_generated_by_one (K : Type*) [Field K] :
    Submodule.span K ({(1 : K)} : Set K) = ⊤ := by sorry


theorem q9_transcendental_X (K : Type*) [Field K] :
    Transcendental K (Polynomial.X : K[X]) := by sorry

end Exercises.FieldTheory.Extensions
