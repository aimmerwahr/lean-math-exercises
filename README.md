# lean-math-exercises

This repo collects math exercises grouped by area, loosely following Mathlib's structure. The author created it in the hope of making mathematics more open and accessible to everyone — practice and feedback are an indispensable part of learning. Contributions are welcome.

## Layout

- `Exercises/` — the sheets you work from: statements with the proof left as `sorry`.
- `Solutions/` — the same statements with complete proofs, to compare against.

Both trees mirror Mathlib's directory structure (e.g. `Exercises/LinearAlgebra/`).
Each area folder has an overview file (`Exercises/<Area>/<Area>.md`) with its scope,
references, and topic map. See for example [Linear Algebra](Exercises/LinearAlgebra/LinearAlgebra.md).
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

Keep two empty lines between consecutive exercise declarations in both `Exercises/` and
`Solutions/` files.

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
