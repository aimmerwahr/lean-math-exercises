import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exercises — GroupTheory / Groups

A **group** is a set with an associative operation, an identity, and inverses — symmetry stripped
to three axioms. Those three lines already force a great deal: the identity and each inverse are
**unique**, inverses reverse order (`(a * b)⁻¹ = b⁻¹ * a⁻¹`), and one can **cancel**
(`a * b = a * c ⇒ b = c`). A **subgroup** is a subset that is itself a group under the same
operation — equivalently a nonempty subset closed under "multiply and invert". Subgroups ordered by
inclusion form a **lattice**: the intersection of subgroups is always a subgroup, while the
set-theoretic union usually is **not**. Two numbers measure a group's size — the **order** `|G|` of
the group and the **order** of an element (the least `n > 0` with `gⁿ = e`, if one exists). When the
operation commutes the group is **abelian**.

Prove each statement yourself; the canonical proofs live in `Solutions/GroupTheory/01Groups.lean`. Do
**not** commit your proofs into this file.

Some exercises ask you to prove *without using* a particular lemma (e.g. "Prove without using
`mul_inv_rev`") — the point is to rebuild that result from more primitive facts. These bans are
enforced automatically when you build the project: if a proof uses a banned lemma (directly or via
`simp`/`omega`/`decide`) the build fails. You don't need to do anything to enable it.
-/

namespace Exercises.GroupTheory.Groups

variable {G : Type*} [Group G]

/-!
## Potentially helpful results

Basic tools you may want while solving the exercises below. **Hover** any name (or place the cursor
on the `#check` line and read the infoview) to see its exact statement.
-/
section

-- Cancellation on the left and on the right.
#check @mul_left_cancel
#check @mul_right_cancel

-- Recognising inverses, and the two cancellation identities `a * a⁻¹ = 1`, `a⁻¹ * a = 1`.
#check @inv_eq_of_mul_eq_one_right
#check @eq_inv_of_mul_eq_one_left
#check @mul_inv_cancel
#check @inv_mul_cancel

-- Placing an element into a join of subgroups, and unpacking a failed inclusion.
#check @Subgroup.mem_sup_left
#check @Subgroup.mem_sup_right
#check @SetLike.not_le_iff_exists
#check @SetLike.mem_coe

-- Pinning down an additive order, and finding a second element once a finite type is large enough.
#check @addOrderOf_eq_iff
#check @Fintype.exists_ne_of_one_lt_card
#check @Fintype.card_congr

-- Passing to the opposite group.
#check @MulOpposite.op
#check @MulOpposite.unop

end

/-- **Question 1.**

Inverses are unique: if `a * b = 1` and `a * c = 1`, then `b = c`. -/
theorem q1_inv_unique {a b c : G} (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  sorry


/-- **Question 2.**

The inverse of a product reverses the factors: `(a * b)⁻¹ = b⁻¹ * a⁻¹`.

Prove without using `mul_inv_rev`. -/
theorem q2_inv_mul_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry


/-- **Question 3.**

The centre of `G` — the elements commuting with everything — is a subgroup: there is a subgroup
whose underlying set is `{a | ∀ g, a * g = g * a}`.

Prove without using `Subgroup.center`. -/
theorem q3_center_isSubgroup :
    ∃ H : Subgroup G, (↑H : Set G) = {a | ∀ g, a * g = g * a} := by
  sorry


/-- **Question 4.**

In the additive group `ZMod 12`, the element `3` has order `4`.

(`addOrderOf x` is the least `n > 0` with `n • x = 0`.) -/
theorem q4_orderOf_concrete : addOrderOf (3 : ZMod 12) = 4 := by
  sorry


/-- **Question 5.**

If `x * x = 1` for every `x`, then `G` is abelian. -/
theorem q5_sq_eq_one_abelian (h : ∀ x : G, x * x = 1) : ∀ a b : G, a * b = b * a := by
  sorry


/-- **Question 6.**

The union of two subgroups is itself a subgroup iff one of them contains the other.

We encode "the union is a subgroup" as the set equality `↑H ∪ ↑K = ↑(H ⊔ K)`: the left side is the
ordinary union of the two underlying sets, the right side is the underlying set of the smallest
subgroup containing both. A subset is a subgroup exactly when it equals the subgroup it generates,
so this equality says precisely that `↑H ∪ ↑K` is already a subgroup. -/
theorem q6_union_isSubgroup_iff (H K : Subgroup G) :
    (↑H ∪ ↑K : Set G) = ↑(H ⊔ K) ↔ H ≤ K ∨ K ≤ H := by
  sorry


/-- **Question 7.**

If `(a * b) * (a * b) = (a * a) * (b * b)` for all `a, b`, then `G` is abelian. -/
theorem q7_mul_sq_abelian (h : ∀ a b : G, (a * b) * (a * b) = (a * a) * (b * b)) :
    ∀ a b : G, a * b = b * a := by
  sorry


/-- **Question 8.**

The **quaternion group** `Q₈` is the eight-element group `{±1, ±i, ±j, ±k}` with `i² = j² = k² = -1`
and `i * j = k`. In Mathlib it is `QuaternionGroup 2`, whose elements are written `a m` and `xa m`
(for `m : ZMod 4`); under this encoding `i = a 1` and `j = xa 0`.

Show that `Q₈` is non-abelian by checking that `i` and `j` do not commute. -/
theorem q8_q8_noncommutative :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0
      ≠ QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  sorry


/-- **Question 9.**

Given any family of subgroups `(Hᵢ)`, their intersection `⋂ᵢ Hᵢ` is a subgroup, and it is the
**greatest lower bound** of the family: it lies below every `Hᵢ`, and any subgroup lying below every
`Hᵢ` lies below it. (Together with the dual least upper bound, this is what makes the subgroups of
`G` a complete lattice.)

Prove without using the packaged `CompleteLattice (Subgroup G)` structure or `Subgroup.instInfSet`. -/
theorem q9_subgroup_inter_glb {ι : Type*} (H : ι → Subgroup G) :
    ∃ K : Subgroup G, (∀ i, K ≤ H i) ∧ (∀ L : Subgroup G, (∀ i, L ≤ H i) → L ≤ K) := by
  sorry

end Exercises.GroupTheory.Groups
