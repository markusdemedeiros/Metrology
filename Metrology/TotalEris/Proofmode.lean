module

public import Metrology.TotalEris.TotalLifting

@[expose] public section

/-!
# Eris proofmode tactics

Port of `clutch/theories/eris/proofmode.v` plus the underlying
`prob_lang/wp_tactics.v`. Provides `wp_*` / `twp_*` macros that
operate on `pglWp` and `tglWp` goals.

Currently each `twp_*` macro expands to a single `iapply` against the
corresponding lifting lemma in `TotalLifting.lean`. The lifting lemmas
are all proved (no `sorry`s in the dependency chain). Higher-level
tactics like `wp_pures` (multi-step reduction) and `wp_apply` (bind +
apply) compose these atomic moves.

Mirrors `Metrology/Approxis/RelTactics.lean` in structure. -/

namespace ProbLang
namespace TotalEris

open Iris Iris.BI Iris.ProofMode

/-! ### Value / return -/

-- `twp_value` now lives in `WpTactics.lean` as an elaborator tactic that detects values
-- semantically (via `toVal?`), so it works on raw `.lit`/`.lam`/… values. The old macro
-- `iapply ErisWpGS.tglWp_value` only matched a syntactic `Exp.ofVal v`.

/-! ### Pure-step tactics

`twp_pure` is the bare macro and works only when the typeclass search for
the `PureExec_discrete` instance can fire without seeing metavariables. For the
common `(λ. _) v` beta-step pattern, this requires `v` to be syntactically
present in the goal. If `twp_pure` fails (typically with "max recursion"
or "Tactic `assumption` failed"), fall back to the explicit form:

```
iapply (ErisWpGS.twp_pure_step_fupd
  (n := 1) (e₁ := <full LHS>) (e₂ := <full RHS>) (φ := <isValue>) ⟨IsVal.lit⟩)
```

— pinning enough arguments lets the relevant `PureExec_discrete` instance unify. -/

-- NOTE: `twp_pure`/`twp_pures` are now elaborator tactics in `WpTactics.lean` that
-- locate the redex and its evaluation context automatically. The old metavar-fragile
-- macros are retired:
--   syntax "twp_pure" : tactic
--   macro_rules | `(tactic| twp_pure) => `(tactic| iapply (ErisWpGS.twp_pure_step_fupd _ (by trivial)))
--   syntax "twp_pures" : tactic
--   macro_rules | `(tactic| twp_pures) => `(tactic| (try repeat twp_pure))

/-- `twp_pure_at <e₁> ↦ <e₂>` — explicit pure-step with both endpoints
pinned. Use when `twp_pure`'s implicit `PureExec_discrete` synthesis fails because
typeclass search can't see through an opaque definition in the LHS. The
precondition `φ` is left implicit (synthesized from the chosen
`PureExec_discrete` instance) and `Hφ` is discharged by the shared `is_value`
tactic — covering `True` (e.g. `pureExec_cond_*_discrete`), value-hood
(`pureExec_app_*`), and the binop/unop/scrut `∧`-conjunctions. Use the `by <h>`
variant below only when the side condition is something `is_value` can't close. -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ (by is_value)))

/-- `twp_pure_at <e₁> ↦ <e₂> by <hφ>` — variant with an explicit proof of
the `PureExec_discrete` precondition (needed when `trivial` can't discharge it,
e.g., for `pureExec_binop_discrete` whose `φ` is a value-and-equation conjunction). -/
macro "twp_pure_at " e1:term:max " ↦ " e2:term:max " by " h:term : tactic =>
  `(tactic| iapply (ErisWpGS.twp_pure_step_fupd
      (n := 1) (e₁ := $e1) (e₂ := $e2) _ $h))

-- `twp_lam` now lives in `WpTactics.lean` (alias for the elaborator `twp_pure`).

/-! ### Structural / bind -/

-- NOTE: `twp_bind` is now an elaborator tactic in `WpTactics.lean` that discovers
-- the evaluation context automatically (`twp_bind <focus : pl_exp>`), superseding the
-- old macro that required an explicit `K`:
--   macro "twp_bind " K:term : tactic => `(tactic| iapply (ErisWpGS.tglWp_bind (K := $K)))

/-- `twp_apply <L>` — plain `iapply L`. Use for top-level applications. -/
macro "twp_apply " L:term : tactic =>
  `(tactic| iapply ($L : _))

/-! ### Aliases that match Rocq's `wp_*` (since `pgl_wp` is the
"default" WP in eris). These delegate to the `twp_*` variants — once
`Lifting.lean` (partial) is filled in, separate `wp_*` versions can be
added. -/

-- `wp_value` now lives in `WpTactics.lean` (alongside `twp_value`).

-- NOTE(iris-bump): the bumped iris HeapLang ProofMode now defines `wp_pure`/`wp_pures`
-- macros, which collide with these (unused) total-WP aliases. Disabled pending the
-- planned rewrite of this file to clone iris's elaborator-based `wp_*` tactics.
-- syntax "wp_pure" : tactic
-- macro_rules
--   | `(tactic| wp_pure) => `(tactic| twp_pure)

-- syntax "wp_pures" : tactic
-- macro_rules
--   | `(tactic| wp_pures) => `(tactic| twp_pures)

-- `wp_lam` now lives in `WpTactics.lean` (alongside `twp_lam`).

macro "wp_apply " L:term : tactic =>
  `(tactic| twp_apply $L)

end TotalEris
end ProbLang
