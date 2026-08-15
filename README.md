# lean-math-exercises

This repository collects mathematical exercises grouped by area, loosely following Mathlib's structure. The author created it with the hope of making mathematics more open and accessible to everyone — practice and feedback are indispensable parts of learning. We hope it benefits both students learning mathematics and people familiar with mathematics who are learning Lean.

## Layout

- `Exercises/` — the sheets you work from: statements with the proof left as `sorry`.
- `Solutions/` — the same statements with complete proofs, to compare against.

Both trees mirror Mathlib's directory structure (e.g. `Exercises/LinearAlgebra/`).
Each subject overview in an area folder has a `00`-prefixed filename
(`Exercises/<Area>/00<Subject>.md`) so it sorts before the numbered sheets. It records the
subject's scope, references, and topic map. See for example
[Linear Algebra](Exercises/LinearAlgebra/00LinearAlgebra.md).
For general Lean proof patterns used across the exercise areas, see [Exercises/Toolbox.lean](Exercises/Toolbox.lean).

## Setup

Requires [Lean 4 with `elan`](https://leanprover-community.github.io/get_started.html).
The toolchain and Mathlib version are pinned in `lean-toolchain` and `lakefile.toml`.

```bash
lake update        # resolve dependencies
lake exe cache get # download prebuilt Mathlib (avoids a multi-hour build)
lake build         # build the project
```

## Working an exercise

1. Open a sheet under `Exercises/`, e.g. `Exercises/LinearAlgebra/01Subspaces.lean`.
2. Each statement has its informal question in the docstring above it. Replace `sorry`
   with your proof.
3. (Optional) When you finish — or if you get stuck — compare with the matching file under `Solutions/`.

Each sheet opens with a **Potentially helpful results** section — hover any `#check`ed
name to see its statement.

Some exercises ask you to prove a result *without* a particular lemma, to rebuild it
from more primitive facts. These bans are enforced on `lake build`: a proof using a
banned lemma (even via `simp`/`omega`/`exact?`) fails to compile. 

Don't commit your own proofs into `Exercises/` files — keep them as
statements-with-`sorry`. (`sorry` is a warning, not an error, so the sheets still build.)

Note: AI can trivialize almost any exercise here, but doing so defeats the point of learning — and standard solutions are already provided anyway.

## Fast iteration

`lake env lean Exercises/LinearAlgebra/01Subspaces.lean` typechecks one file against the
cached Mathlib build — much faster than `lake build` while iterating a single proof.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

This project is licensed under the [Apache License, Version 2.0](LICENSE).
Copyright 2026 aimmerwahr. Contributions intentionally submitted for inclusion in the
project are licensed under the same terms. Dependencies, including Mathlib,
remain under their own licenses.
