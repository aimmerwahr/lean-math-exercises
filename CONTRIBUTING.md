# Contributing

- Corrections and improvements to existing exercises are always welcome.
- Any new exercise must be created or approved by someone with adequate domain knowledge and qualifications. AI generation is fine as long as a human stays in the loop to maintain quality.
- Prioritize standard undergraduate mathematics over advanced domains, and prefer areas with a solid foundation in Mathlib over those without.

## Structure

Every `Exercises/A/B/C.lean` has a matching `Solutions/A/B/C.lean` at the same path.
Both trees mirror Mathlib's directory hierarchy.

- Place files by Mathlib area: the area is a folder, the topic is a file under it —
  e.g. `Exercises/LinearAlgebra/Determinants.lean`. Group by course topic, not by
  Mathlib source file. Create an area folder only when you add an exercise for it.
- Each area folder has one overview: `Exercises/<Area>/<Area>.md` (scope, references,
  corresponding Mathlib modules, topic dependency graph). Committed under `Exercises/`
  only.

## Conventions

- **Namespace = module path.** `Exercises/LinearAlgebra/Determinants.lean` uses
  `namespace Exercises.LinearAlgebra.Determinants`; its solution uses
  `namespace Solutions.LinearAlgebra.Determinants`.
- **Declaration names: `q<N>_<snake_case_name>`**, numbered per file from `q1`
  (e.g. `q1_det_of_zero_matrix_eq_zero`). The number and name must be identical in the
  paired exercise and solution files — they differ only by the namespace root.
- Each exercise carries its informal statement in a `/-- … -/` docstring above the
  declaration, opening with a `**Question N.**` line.
- Each sheet opens with a **Potentially helpful results** `#check` toolbox — usable
  library lemmas, never a banned one.
- Import what you need at the top of each file (typically `import Mathlib.Tactic` plus
  the specific modules used).

## Lemma bans

To ask for a result proved *without* a given lemma, add a check under
`Meta/Checks/<Area>/<Topic>.lean` using `assert_not_uses` (see `Meta/BanCheck.lean`).
It inspects the proof term, so `simp`/`omega`/`exact?` cannot smuggle a banned lemma
past it. The check runs on `lake build`.

## Before submitting

- Every exercise must come with a solution, to confirm it is solvable.
- `lake build` passes (exercise sheets build with only `sorry` warnings; solutions
  build clean).
- Solutions are sorry-free. Check hygiene with `#print axioms <decl>` — expect only
  `propext` / `Classical.choice` / `Quot.sound`, never `sorryAx`.
- You are encouraged to use AI to check against the conventions above.
