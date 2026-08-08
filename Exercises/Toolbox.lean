import Mathlib.Tactic

/-!
# Lean Toolbox

This is a collection of small, general-purpose Lean facts and proof patterns used throughout the
exercise sheets. It is not specific to one mathematical topic.

## Basic proof steps

Use `rfl` when both sides of an equality reduce to the same expression:
```lean
example (a : Nat) : a + 0 = a := by
  rfl
```

When used as a pattern while unpacking an equality, `rfl` substitutes one side for the other
throughout the goal and context:
```lean
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rcases h with rfl
  rfl
```
This is especially useful in patterns such as `rintro ⟨x, hx, rfl⟩`, where the final equality
replaces the target variable by the expression constructed from `x`.

Use `rw [h]` for a selected, directed rewrite:
```lean
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

Use `nth_rw n [h]` when the same rewrite matches several places but only the `n`th occurrence
should change:
```lean
example (a b : Nat) (h : a = b) : a + a = a + b := by
  nth_rw 2 [h]
```

Use `constructor` when the goal is a conjunction or an equivalence:
```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ
```

Use `refine` for the same situation when you can provide part of a proof and want Lean to leave
the rest as an explicit goal:
```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨hP, ?_⟩
  exact hQ
```

When more than one goal is open, `swap` exchanges the first two goals:
```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  swap
  · exact hQ
  · exact hP
```

`rotate_left` moves the first goal to the end, while `rotate_right` moves the last goal to the
front. They only change which goal Lean displays; they do not change the mathematics:
```lean
example (P Q R : Prop) (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · exact hQ
  · exact hR
  · exact hP

example (P Q R : Prop) (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  refine ⟨?_, ?_, ?_⟩
  rotate_right
  · exact hR
  · exact hP
  · exact hQ
```

Use `intro` to name an assumption without changing its shape. Use `rintro` when you want to
introduce and destructure it in one step:
```lean
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1

example (P Q : Prop) : P ∧ Q → P := by
  rintro ⟨hP, _⟩
  exact hP
```

Use `revert` to move local variables or hypotheses back into the goal before introducing them
again, which is useful when the order of generalization matters:
```lean
example (n : Nat) (h : n = 0) : ∀ m : Nat, n + m = m := by
  revert h
  intro h m
  simp [h]
```

Use `rcases h with ⟨x, hx⟩` or `obtain ⟨x, hx⟩ := h` to unpack an existential or conjunction
that is already available in the context.

## Simplification and rewriting

Use `simp` for routine rewrites, identities, and membership facts:
```lean
have h0 : f 0 = 0 := by simp
```

`simpa` means “simplify, then close the goal by assumption.” In this example it simplifies both
the goal and the type of `h`, then uses `h`:
```lean
example (n : Nat) (h : n + 0 = 3) : n = 3 := by
  simpa using h
```

Use `simp_rw [h]` when a rewrite should be applied recursively throughout an expression:
```lean
example (a b : Nat) (h : a = b) : a + a = b + b := by
  simp_rw [h]
```
Unlike `repeat rw [h]`, which repeats only the named rewrite steps, `simp_rw` uses `simp`'s
recursive rewriting procedure. It descends into subexpressions and continues after a rewrite has
exposed further occurrences. Prefer `rw` when you want one controlled rewrite; use `simp_rw` for
a rewrite rule that should act everywhere.

## Order and equality

`le_antisymm` proves `A = B` from inequalities `A ≤ B` and `B ≤ A`:
```lean
example (A B : Nat) (hAB : A ≤ B) (hBA : B ≤ A) : A = B := by
  exact le_antisymm hAB hBA
```

Chain inequalities to prove `A ≤ C`:
```lean
example (A B C : Nat) (hAB : A ≤ B) (hBC : B ≤ C) : A ≤ C := by
  exact hAB.trans hBC
```

`sub_eq_zero` changes an additive equality `a - b = 0` into `a = b`:
```lean
example (a b : Int) (h : a - b = 0) : a = b := by
  exact sub_eq_zero.mp h
```

## Algebra and finite cases

Use `abel` for equalities built only from addition, subtraction, and negation in a commutative
additive group:
```lean
have : (a + b) - a = b := by abel
```
Use `linear_combination` to combine linear equalities:
```lean
-- Given ha : a = 0 and hb : b = 0:
linear_combination ha + hb
```
Use `omega` for arithmetic over natural numbers and integers:
```lean
-- Given h : m + n = 7 and hm : m = 3:
omega
```
For functions on a finite index type, prove equality coordinatewise:
```lean
funext i
fin_cases i <;> simp
```
-/

namespace Exercises.Toolbox

section

#check @le_antisymm
#check @le_trans
#check @sub_eq_zero
#check @eq_comm

end

end Exercises.Toolbox
