import Exercises.LinearAlgebra.«04Dimension»
import Solutions.LinearAlgebra.«04Dimension»
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / Dimension

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans in the exercise docstrings, against both the reader's
attempts and the shipped canonical solutions.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.Dimension.q1_rigidity [Submodule.eq_of_le_of_finrank_eq]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.Dimension.q1_rigidity [Submodule.eq_of_le_of_finrank_eq]
