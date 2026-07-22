# lean-math-exercises


## Toolchain

- Lean: `leanprover/lean4:v4.33.0-rc1` (see `lean-toolchain`)
- Mathlib: pinned in `lakefile.toml` to a commit whose build cache is available,
  matching the neighboring `lean-eval-problems` repo.

## First build

```bash
lake update        # resolve deps, write lake-manifest.json
lake exe cache get # download prebuilt Mathlib oleans (fast; avoids a full build)
lake build         # build this project
```
