import Exercises.LinearAlgebra.Determinants
import Solutions.LinearAlgebra.Determinants
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / Determinants

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans in the exercise docstrings, against both the reader's
attempts and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.Determinants.q3_det_mul_concrete [Matrix.det_mul]
assert_not_uses Exercises.LinearAlgebra.Determinants.q8_det_transpose [Matrix.det_transpose]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.Determinants.q3_det_mul_concrete [Matrix.det_mul]
assert_not_uses Solutions.LinearAlgebra.Determinants.q8_det_transpose [Matrix.det_transpose]
