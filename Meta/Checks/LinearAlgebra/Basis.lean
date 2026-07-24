import Exercises.LinearAlgebra.Basis
import Solutions.LinearAlgebra.Basis
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / Basis

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against both the
reader's own attempts in `Exercises/LinearAlgebra/Basis.lean` (the build fails here if a proof
uses a banned lemma) and the shipped canonical proofs in `Solutions/LinearAlgebra/Basis.lean`
(a permanent regression guard).
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.Basis.q1_coords_unique [Module.Basis.ext_elem]
assert_not_uses Exercises.LinearAlgebra.Basis.q2_map_determined [Module.Basis.ext]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.Basis.q1_coords_unique [Module.Basis.ext_elem]
assert_not_uses Solutions.LinearAlgebra.Basis.q2_map_determined [Module.Basis.ext]
