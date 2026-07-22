import Lean

/-!
# `assert_not_uses` — enforced lemma bans

`assert_not_uses foo [bar, baz]` fails to compile if the proof term of the declaration
`foo` references any of the constants `bar`, `baz`. It is used to enforce that an
exercise's solution is proved *without* a trivializing Mathlib lemma.

Mechanism (same idea as the Lean Game Server's `collectUsedInventory`): look up the
declaration's proof term and collect the constants it uses via `Expr.getUsedConstants`,
then error if any banned constant appears. Because a lemma pulled in by `simp`/`omega`/
`exact?` still shows up as a constant in the resulting term, automation cannot smuggle a
banned lemma past this check.

The check is *direct*, not transitive: citing an earlier exercise that itself uses a
banned lemma is fine — only the declaration's own proof term is inspected.

Limitations: `decide`/`native_decide` can settle a goal by raw computation without naming
the lemma, and a `@[reducible]` definition may unfold and not appear by name. These are
edge cases for lemma-level bans.
-/

namespace Meta

open Lean Elab Command

/-- `assert_not_uses foo [bar, baz]` errors if the proof term of `foo` uses `bar`/`baz`. -/
elab "assert_not_uses " decl:ident " [" banned:ident,* "]" : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  let env ← getEnv
  let some info := env.find? declName
    | throwErrorAt decl s!"unknown declaration '{declName}'"
  let value ← match info with
    | .thmInfo v => pure v.value
    | .defnInfo v => pure v.value
    | .opaqueInfo v => pure v.value
    | _ => throwErrorAt decl s!"'{declName}' has no proof term to inspect"
  let used : NameSet := value.getUsedConstants.foldl (init := {}) (·.insert ·)
  for b in banned.getElems do
    let bName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if used.contains bName then
      throwErrorAt b s!"'{declName}' uses banned lemma '{bName}'"

end Meta
