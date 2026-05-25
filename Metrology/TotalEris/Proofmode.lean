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

syntax "twp_value" : tactic
macro_rules
  | `(tactic| twp_value) => `(tactic| iapply ErisWpGS.tglWp_value)

/-! ### Pure-step tactics

`twp_pure` is the bare macro and works only when the typeclass search for
the `PureExec` instance can fire without seeing metavariables. For the
common `(λ. _) v` beta-step pattern, this requires `v` to be syntactically
present in the goal. If `twp_pure` fails (typically with "max recursion"
or "Tactic `assumption` failed"), fall back to the explicit form:

```
iapply (ErisWpGS.twp_pure_step_fupd
  (n := 1) (e₁ := <full LHS>) (e₂ := <full RHS>) (φ := <isValue>) ⟨IsVal.lit⟩)
```

— pinning enough arguments lets the relevant `PureExec` instance unify. -/

syntax "twp_pure" : tactic
macro_rules
  | `(tactic| twp_pure) =>
    `(tactic| iapply (ErisWpGS.twp_pure_step_fupd _ (by trivial)))

syntax "twp_pures" : tactic
macro_rules
  | `(tactic| twp_pures) =>
    `(tactic| (try repeat twp_pure))

syntax "twp_lam" : tactic
macro_rules
  | `(tactic| twp_lam) =>
    `(tactic| twp_pure)

/-! ### Structural / bind -/

/-- `twp_bind <K>` rebases the WP goal at `K.fill e` to `e` with the
continuation wrapped through `K`. Useful for focusing on a subexpression. -/
macro "twp_bind " K:term : tactic =>
  `(tactic| iapply (ErisWpGS.tglWp_bind (K := $K)))

/-- `twp_apply <L>` — plain `iapply L`. Use for top-level applications. -/
macro "twp_apply " L:term : tactic =>
  `(tactic| iapply ($L : _))

/-- `twp_apply_at <K> <L>` — combined bind+apply. Equivalent to
`twp_bind <K>; iapply <L>`. Use when the rule `L` is for a primitive that
appears inside an evaluation context `K` in the current goal. -/
macro "twp_apply_at " K:term ", " L:term : tactic =>
  `(tactic| (twp_bind $K; iapply ($L : _)))

/-! ### Aliases that match Rocq's `wp_*` (since `pgl_wp` is the
"default" WP in eris). These delegate to the `twp_*` variants — once
`Lifting.lean` (partial) is filled in, separate `wp_*` versions can be
added. -/

syntax "wp_value" : tactic
macro_rules
  | `(tactic| wp_value) => `(tactic| twp_value)

syntax "wp_pure" : tactic
macro_rules
  | `(tactic| wp_pure) => `(tactic| twp_pure)

syntax "wp_pures" : tactic
macro_rules
  | `(tactic| wp_pures) => `(tactic| twp_pures)

syntax "wp_lam" : tactic
macro_rules
  | `(tactic| wp_lam) => `(tactic| twp_lam)

macro "wp_apply " L:term : tactic =>
  `(tactic| twp_apply $L)

end TotalEris
end ProbLang
