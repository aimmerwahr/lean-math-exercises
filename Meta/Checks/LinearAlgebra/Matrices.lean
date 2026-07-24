import Exercises.LinearAlgebra.Matrices
import Solutions.LinearAlgebra.Matrices
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / Matrices

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans in the exercise docstrings, against both the reader's
attempts and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.Matrices.q4_comp_eq_mul [Matrix.toLin'_mul]
assert_not_uses Exercises.LinearAlgebra.Matrices.q5_one_sided_inverse [mul_eq_one_comm]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.Matrices.q4_comp_eq_mul [Matrix.toLin'_mul]
assert_not_uses Solutions.LinearAlgebra.Matrices.q5_one_sided_inverse [mul_eq_one_comm]
