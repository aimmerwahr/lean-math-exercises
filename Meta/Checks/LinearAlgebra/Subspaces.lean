import Exercises.LinearAlgebra.Subspaces
import Solutions.LinearAlgebra.Subspaces
import Meta.BanCheck

/-!
# Internal ban checks — LinearAlgebra / Subspaces

**Not exercise content — you do not need to read or edit this file.**

It enforces the "prove without …" bans stated in the exercise docstrings, against two
targets:

* the **exercise** proofs you write in `Exercises/LinearAlgebra/Subspaces.lean` — building
  the project fails here if your proof uses a banned lemma (directly or via
  `simp`/`omega`/`exact?`); while an exercise is still `sorry` its check is a no-op;
* the **solution** proofs in `Solutions/LinearAlgebra/Subspaces.lean` — a permanent
  regression guard that the shipped solutions keep respecting the bans.
-/

open Meta

-- Exercise proofs (checks the reader's own attempts).
assert_not_uses Exercises.LinearAlgebra.Subspaces.q1_mem_inf_iff [Submodule.mem_inf]
assert_not_uses Exercises.LinearAlgebra.Subspaces.q2_mem_sup_iff [Submodule.mem_sup, Submodule.mem_sup']
assert_not_uses Exercises.LinearAlgebra.Subspaces.q3_sup_le_iff [sup_le, sup_le_iff]
assert_not_uses Exercises.LinearAlgebra.Subspaces.q4_sup_eq_right_iff_le [sup_eq_right, sup_eq_left]
assert_not_uses Exercises.LinearAlgebra.Subspaces.q7_disjoint_iff_forall_eq_zero [Submodule.disjoint_def, disjoint_iff]
assert_not_uses Exercises.LinearAlgebra.Subspaces.q9_modular_law [sup_inf_assoc_of_le]

-- Solution proofs (regression guard on the shipped canonical proofs).
assert_not_uses Solutions.LinearAlgebra.Subspaces.q1_mem_inf_iff [Submodule.mem_inf]
assert_not_uses Solutions.LinearAlgebra.Subspaces.q2_mem_sup_iff [Submodule.mem_sup, Submodule.mem_sup']
assert_not_uses Solutions.LinearAlgebra.Subspaces.q3_sup_le_iff [sup_le, sup_le_iff]
assert_not_uses Solutions.LinearAlgebra.Subspaces.q4_sup_eq_right_iff_le [sup_eq_right, sup_eq_left]
assert_not_uses Solutions.LinearAlgebra.Subspaces.q7_disjoint_iff_forall_eq_zero [Submodule.disjoint_def, disjoint_iff]
assert_not_uses Solutions.LinearAlgebra.Subspaces.q9_modular_law [sup_inf_assoc_of_le]
