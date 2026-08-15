# Contributing

By intentionally submitting a contribution for inclusion in this project, you
agree to license it under the [Apache License, Version 2.0](LICENSE), unless you
and the maintainer agree otherwise in writing. You must have the right to
submit the contribution under these terms.

- Corrections and improvements to existing exercises are always welcome.
- Any new exercise must be created or approved by someone with adequate domain knowledge and qualifications. AI generation is fine as long as a human stays in the loop to maintain quality.
- Prioritize standard undergraduate mathematics over advanced domains, and prefer areas with a solid foundation in Mathlib over those without.

## Structure

Every `Exercises/<Area>/<NNTopic>.lean` has a matching
`Solutions/<Area>/<NNTopic>.lean` at the same path, where `NN` is the two-digit sheet index.
Both trees mirror Mathlib's directory hierarchy.

- Place files by Mathlib area: the area is a folder, the topic is a file under it —
  e.g. `Exercises/LinearAlgebra/07Determinants.lean`. Group by course topic, not by
  Mathlib source file. Create an area folder only when you add an exercise for it.
- Each subject overview in an area folder is `00`-prefixed:
  `Exercises/<Area>/00<Subject>.md` (scope, references, corresponding Mathlib modules, topic
  dependency graph). An area with multiple subjects gives **every** overview this prefix. These
  files sort before the numbered sheets and are committed under `Exercises/` only.

## Conventions

- **Namespace = topic name.** `Exercises/LinearAlgebra/07Determinants.lean` uses
  `namespace Exercises.LinearAlgebra.Determinants`; its solution uses
  `namespace Solutions.LinearAlgebra.Determinants`.
- **Declaration names: `q<N>_<snake_case_name>`**, numbered per file from `q1`
  (e.g. `q1_det_of_zero_matrix_eq_zero`). The number and name must be identical in the
  paired exercise and solution files — they differ only by the namespace root.
- Each exercise carries its informal statement in a `/-- … -/` docstring above the
  declaration, opening with a `**Question N.**` line.
- Keep two empty lines between consecutive exercise declarations in both the `Exercises/` and
  `Solutions/` trees.
- Each sheet opens with a **Potentially helpful results** `#check` toolbox — usable
  library lemmas, never a banned one.
- Import what you need at the top of each file (typically `import Mathlib.Tactic` plus
  the specific modules used).

## Lemma bans

To ask for a result proved *without* a given lemma, add a check under
`Meta/Checks/<Area>/<NNTopic>.lean` using `assert_not_uses` (see `Meta/BanCheck.lean`).
It inspects the proof term, so `simp`/`omega`/`exact?` cannot smuggle a banned lemma
past it. The check runs on `lake build`.

## Before submitting

- Every exercise must come with a solution, to confirm it is solvable.
- `lake build` passes (exercise sheets build with only `sorry` warnings; solutions
  build clean).
- `bash Meta/scripts/style-lint.sh` passes. It enforces the mechanical formatting conventions,
  including explicit `@` toolbox checks, standalone exercise `sorry`s, question spacing, and
  solution independence from exercise files.
- Solutions are sorry-free. Check hygiene with `#print axioms <decl>` — expect only
  `propext` / `Classical.choice` / `Quot.sound`, never `sorryAx`.
- You are encouraged to use AI to check against the conventions above.
