import Exercises.LinearAlgebra.«05LinearMaps»
import Solutions.LinearAlgebra.«05LinearMaps»
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / LinearMaps

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans in the exercise docstrings, against both the reader's
attempts and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.LinearMaps.q2_injective_iff_ker [LinearMap.ker_eq_bot]
assert_not_uses Exercises.LinearAlgebra.LinearMaps.q3_surjective_iff_range [LinearMap.range_eq_top]
assert_not_uses Exercises.LinearAlgebra.LinearMaps.q4_inj_iff_surj [LinearMap.injective_iff_surjective]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.LinearMaps.q2_injective_iff_ker [LinearMap.ker_eq_bot]
assert_not_uses Solutions.LinearAlgebra.LinearMaps.q3_surjective_iff_range [LinearMap.range_eq_top]
assert_not_uses Solutions.LinearAlgebra.LinearMaps.q4_inj_iff_surj [LinearMap.injective_iff_surjective]
