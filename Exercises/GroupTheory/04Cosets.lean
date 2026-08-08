import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Cosets & Lagrange

For a subgroup `H ≤ G`, the **cosets** `gH` partition `G` into blocks that are all the **same size**
as `H`. Counting the blocks gives the **index** `[G : H]`, and the partition immediately yields
**Lagrange's theorem**: `|G| = |H| · [G : H]`, so `|H|` divides `|G|`. The consequences are out of
proportion to the simplicity of the argument: the order of every element divides `|G|`; a group of
**prime order is cyclic**; and, specialised to `ℤ/n`, Lagrange becomes **Fermat's little theorem**
and **Euler's theorem**.

Prove each statement yourself; the canonical proofs live in `Solutions/GroupTheory/04Cosets.lean`. Do
**not** commit your proofs into this file.

Several exercises ask you to prove *without using* a particular one-shot lemma — the point is to
derive the result from Lagrange (and its predecessors) yourself. The bans are enforced when you
build the project.
-/

namespace Exercises.GroupTheory.Cosets

open Pointwise

variable {G : Type*} [Group G]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name to see its exact
statement.
-/
section

-- The coset partition and Lagrange's counting equation.
#check @Set.ncard_smul_set
#check @Subgroup.card_eq_card_quotient_mul_card_subgroup

-- Element order via the cyclic subgroup it generates, and recognising a generator.
#check @Nat.card_zpowers
#check @orderOf_eq_one_iff
#check @isCyclic_of_orderOf_eq_card
#check @orderOf_dvd_iff_pow_eq_one

-- The unit group of `ZMod n`: its size, and moving between a unit and its value.
#check @ZMod.card_units_eq_totient
#check @Nat.totient_prime
#check @isUnit_iff_ne_zero
#check @Units.val_pow_eq_pow_val

end

/-- **Question 1.**

Every left coset `gH` has the same size as `H`: the coset `g • ↑H` and `↑H` have equal cardinality
(`Set.ncard`). -/
theorem q1_coset_card (g : G) (H : Subgroup G) :
    (g • (H : Set G)).ncard = (H : Set G).ncard := by
  sorry


/-- **Question 2.**

Lagrange's theorem: the order of a subgroup divides the order of the group.

Prove without using `Subgroup.card_subgroup_dvd_card`. -/
theorem q2_lagrange [Finite G] (H : Subgroup G) : Nat.card H ∣ Nat.card G := by
  sorry


/-- **Question 3.**

The order of an element divides the order of the group.

Prove without using `orderOf_dvd_card`. -/
theorem q3_orderOf_dvd_card [Finite G] (g : G) : orderOf g ∣ Nat.card G := by
  sorry


/-- **Question 4.**

A group of prime order is cyclic.

Prove without using `isCyclic_of_prime_card`. -/
theorem q4_prime_order_cyclic [Finite G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p) : IsCyclic G := by
  sorry


/-- **Question 5.**

Fermat's little theorem: for prime `p` and `a ≠ 0` in `ZMod p`, `a^(p-1) = 1`.

Prove without using `ZMod.pow_card_sub_one_eq_one`. -/
theorem q5_fermat_little {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  sorry


/-- **Question 6.**

Euler's theorem: if `a` is a unit of `ZMod n`, then `a^{φ(n)} = 1`.

Prove without using `ZMod.pow_totient`. -/
theorem q6_euler {n : ℕ} [NeZero n] (a : ZMod n) (ha : IsUnit a) :
    a ^ n.totient = 1 := by
  sorry


/-- **Question 7.**

A concrete Lagrange check: `S₃` has `6` elements and its alternating subgroup `A₃` has `3`, so `A₃`
has `6 / 3 = 2` cosets. -/
theorem q7_cosets_count :
    Nat.card (Equiv.Perm (Fin 3)) = 6 ∧ Nat.card (alternatingGroup (Fin 3)) = 3 := by
  sorry


/-- **Question 8.**

A nontrivial finite group whose only subgroups are `{e}` and `G` has prime order. -/
theorem q8_no_proper_subgroups [Finite G] [Nontrivial G]
    (h : ∀ K : Subgroup G, K = ⊥ ∨ K = ⊤) : (Nat.card G).Prime := by
  sorry

end Exercises.GroupTheory.Cosets
