import Exercises.LinearAlgebra.Eigenvalues
import Solutions.LinearAlgebra.Eigenvalues
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / Eigenvalues

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans in the exercise docstrings, against both the reader's
attempts and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.Eigenvalues.q1_eigen_iff_ker [Module.End.mem_eigenspace_iff]
assert_not_uses Exercises.LinearAlgebra.Eigenvalues.q3_distinct_independent [Module.End.eigenvectors_linearIndependent]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.Eigenvalues.q1_eigen_iff_ker [Module.End.mem_eigenspace_iff]
assert_not_uses Solutions.LinearAlgebra.Eigenvalues.q3_distinct_independent [Module.End.eigenvectors_linearIndependent]
