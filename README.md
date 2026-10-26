# lean-math-exercises

This repository collects mathematical exercises in Lean grouped by area, loosely following Mathlib's structure. The author created it with the hope of making mathematics more open and accessible to everyone — practice and feedback are indispensable parts of learning. We hope it benefits both students learning mathematics and people familiar with mathematics who are learning Lean.

- Currently covered topics: parts of the standard undergraduate curriculum in linear algebra, abstract algebra, topology, and real analysis. See the [table of contents below](#exercise-sheets).
- Planned topics: commutative algebra, category theory/arrow chasing in Lean, etc.
- Topics I would like to see added (hopefully by friendly strangers from the Internet): more linear algebra, Galois theory, complex analysis, and many more.

## Layout

- `Exercises/` — the sheets you work from: statements with the proof left as `sorry`.
- `Solutions/` — the same statements with complete proofs, to compare against.

Both trees mirror Mathlib's directory structure (e.g. `Exercises/LinearAlgebra/`).
Each subject overview in an area folder has a filename prefixed with `00`
(`Exercises/<Area>/00<Subject>.md`) so it sorts before the numbered sheets. It records the
subject's scope, references, and topic map. See for example
[Linear Algebra](Exercises/LinearAlgebra/00LinearAlgebra.md).
For general Lean proof patterns used across the exercise areas, see [Exercises/Toolbox.lean](Exercises/Toolbox.lean).

## For beginners

New to Lean? Start with the [complete getting-started guide](GettingStarted.md).

## Setup

Requires [Lean 4 with `elan`](https://leanprover-community.github.io/get_started.html).
The toolchain and Mathlib version are pinned in `lean-toolchain` and `lakefile.toml`.

```bash
lake update        # resolve dependencies
lake exe cache get # download prebuilt Mathlib (avoids a multi-hour build)
lake build         # build the project
```

## Work on an exercise

1. Open a sheet under `Exercises/`, e.g. `Exercises/LinearAlgebra/01Subspaces.lean`.
2. Each statement has its informal question in the docstring above it. Replace `sorry`
   with your proof.
3. (Optional) When you finish — or if you get stuck — compare with the matching file under `Solutions/`.

Each sheet opens with a **Potentially helpful results** section — hover any `#check`ed
name to see its statement.

Some exercises ask you to prove a result *without* a particular lemma, to rebuild it
from more primitive facts. These bans are enforced during `lake build`: a proof using a
banned lemma (even via `simp`/`omega`/`exact?`) fails to compile.

Don't commit your own proofs into `Exercises/` files — keep them as
statements-with-`sorry`. (`sorry` is a warning, not an error, so the sheets still build.)

Note: AI can trivialize almost any exercise here, but doing so defeats the point of learning — and standard solutions are already provided anyway.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

This project is licensed under the [Apache License, Version 2.0](LICENSE).
Copyright 2026 aimmerwahr. Contributions intentionally submitted for inclusion in the
project are licensed under the same terms. Dependencies, including Mathlib,
remain under their own licenses.

## Exercise sheets

### [Linear algebra](Exercises/LinearAlgebra/00LinearAlgebra.md)

1. [Subspaces](Exercises/LinearAlgebra/01Subspaces.lean)
2. [Span and independence](Exercises/LinearAlgebra/02SpanIndependence.lean)
3. [Basis](Exercises/LinearAlgebra/03Basis.lean)
4. [Dimension](Exercises/LinearAlgebra/04Dimension.lean)
5. [Linear maps](Exercises/LinearAlgebra/05LinearMaps.lean)
6. [Matrices](Exercises/LinearAlgebra/06Matrices.lean)
7. [Determinants](Exercises/LinearAlgebra/07Determinants.lean)
8. [Eigenvalues](Exercises/LinearAlgebra/08Eigenvalues.lean)

### [Group theory](Exercises/GroupTheory/00GroupTheory.md)

1. [Groups](Exercises/GroupTheory/01Groups.lean)
2. [Cyclic groups](Exercises/GroupTheory/02Cyclic.lean)
3. [Permutations](Exercises/GroupTheory/03Permutations.lean)
4. [Cosets and Lagrange's theorem](Exercises/GroupTheory/04Cosets.lean)
5. [Homomorphisms and isomorphisms](Exercises/GroupTheory/05Homomorphisms.lean)
6. [Normal subgroups and quotients](Exercises/GroupTheory/06Quotients.lean)
7. [Group actions](Exercises/GroupTheory/07GroupActions.lean)
8. [Sylow theory](Exercises/GroupTheory/08Sylow.lean)
9. [Finite abelian groups](Exercises/GroupTheory/09FiniteAbelian.lean)

### [Ring theory and commutative algebra](Exercises/RingTheory/00RingTheory.md)

1. [Rings](Exercises/RingTheory/01Rings.lean)
2. [Ideals and quotients](Exercises/RingTheory/02Ideals.lean)
3. [Prime and maximal ideals](Exercises/RingTheory/03PrimeAndMaximalIdeals.lean)

### [Field theory](Exercises/FieldTheory/00FieldTheory.md)

1. [Extensions and degree](Exercises/FieldTheory/01Extensions.lean)
2. [Finite fields](Exercises/FieldTheory/02FiniteFields.lean)
3. [Splitting fields and algebraic roots](Exercises/FieldTheory/03SplittingFields.lean)

### [Topology](Exercises/Topology/00Topology.md)

1. [Metric spaces](Exercises/Topology/01MetricSpaces.lean)
2. [Compactness](Exercises/Topology/02Compactness.lean)
3. [Connectedness](Exercises/Topology/03Connectedness.lean)

### [Analysis](Exercises/Analysis/00Analysis.md)

1. [Order completeness](Exercises/Analysis/01OrderCompleteness.lean)
2. [Real sequences](Exercises/Analysis/02RealSequences.lean)
3. [Series](Exercises/Analysis/03Series.lean)
4. [Continuous functions](Exercises/Analysis/04ContinuousFunctions.lean)
5. [Differentiation](Exercises/Analysis/05Differentiation.lean)
6. [Riemann integration](Exercises/Analysis/06RiemannIntegration.lean)
7. [Function sequences](Exercises/Analysis/07FunctionSequences.lean)
8. [Elementary functions](Exercises/Analysis/08ElementaryFunctions.lean)
