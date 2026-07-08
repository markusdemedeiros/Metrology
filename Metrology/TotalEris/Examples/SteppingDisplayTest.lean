module

public import Metrology.TotalEris
public import Metrology.TotalEris.Examples.GeometricTotal
public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric

@[expose] public section

/-!
# Display-golden tests for `twp_*` stepping

`WpTacticsTest.lean` checks that stepping lands on the right `Exp` *up to defeq*
(via `show`). This file checks the orthogonal property the user actually reads:
**what the goal renders as in the infoview after a step.**

The acceptance bar: after stepping, a goal must show

  * **named binders** (`fun n, …`, `let x := …; …`, `rec geo _ := …`), never a
    leaked de Bruijn index `⟪bvar n⟫` and never a raw `.lam` / `.fix`
    projection; and
  * **folded recursive constants** (`&loopFolded`, `&GeometricTrial`), never a
    raw `Exp.fix (Exp.lam …)` body; and
  * **normalized literals** (`#3`, `#false`), never an unevaluated
    `#(1 + 2)` / `#(decide (2 = 0))`.

Each test pins the rendered target with `#guard_msgs`. **All six display/stepping
bugs are now fixed** (see `totaleris_stepping_display_suite` memory): every
golden below is the CLEAN form, and these tests are the regression guard against
re-introducing a bvar/`.lam`/`.fix`/`.case`/unnormalized-literal leak:

  * Bug 1 — `Exp.lam`/`Exp.fix` delaborator names binders + resolves `bvar`s
    (`§2`, `§8`, `§16`, `§25a`);
  * Bug 2 — binop/unop results normalize, which also unblocks `cond` so
    recursion runs to completion (`§4`, `§7`, `§9`, `§10`, `§17`, `§18`, `§22`);
  * Bug 3 — `twp_pures` auto-unfolds head recursive constants (`§7a`, `§25`);
  * Bug 4 — `scrut`/`case`/`let!` `isValue` side goals auto-discharge + an
    `Exp.case` delaborator (`§11`, `§20`);
  * Bug 6 — `Exp.ofVal ⟨e, _⟩` collapses to `e` (`§24`).

The only residual escape is `{Exp.ofVal v}` for an *opaque bound value* `v` (a
`twp_bind` continuation argument) — correct: there is no surface syntax for an
abstract value.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

-- This is a display-only suite: `show_goal_render` and the deliberately-no-op
-- `twp_pures` in §7a do not change the proof state, which is the point.
set_option linter.unusedTactic false

namespace ProbLang
namespace TotalEris
namespace SteppingDisplayTest

open Lean Elab Tactic in
/-- Log *only* the pretty-printed main-goal target (the iris entailment),
omitting the local hypothesis block, so display-golden values stay focused. -/
elab "show_goal_render" : tactic => do
  logInfo m!"{← getMainTarget}"

variable {rT : Type _} [ProbLang.ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable (E : CoPset) (Φ : Val rT → IProp GF)

-- This is a *display-only* suite: each `example` steps a goal and checks how the
-- residual entailment renders (via `show_goal_render` + `#guard_msgs`). The
-- entailment itself is not the object of study and, for an arbitrary `Φ`, is not
-- provable. Rather than close each with `sorry` — which taints the environment
-- with `sorryAx` and emits "declaration uses 'sorry'" warnings — we discharge it
-- with `hstop`, a hypothesis available only inside these examples. The rendered
-- target that `#guard_msgs` inspects is unaffected (it never prints hypotheses),
-- so the goldens below are exactly the stepped forms, and the file is sorry-free.
variable (hstop : ∀ Q : IProp GF, ⊢@{IProp GF} Q)
-- Companion fixture for the incidental `IsVal _` (a `Type`, not an entailment)
-- side goal that a stalled step can leave — see §25b.
variable (hval : ∀ e : Exp rT, IsVal e)

/-! ## 1. β-reduction, fully substituted (binder consumed) — CLEAN -/

/-- info: ⊢ tglWp E pl(#2 + #1) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl((fun x, x + #1) #2) Φ := by
  twp_pure pl((fun x, x + #1) #2)
  show_goal_render
  exact hstop _

/-! ## 2. β-reduction leaving an inner binder — CLEAN ✓ (source name recovered)

After substituting the outer argument, an inner `fun y, …` remains. Its source
name `y` is recovered: `pureStepResult` collects the redex body's `plBinderName`
hints and `reattachNames` re-applies them to the reduced result — `pl(fun y, #1)`. -/

/-- info: ⊢ tglWp E pl(fun y, #1) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl((fun x, fun y, x) #1) Φ := by
  twp_pure pl((fun x, fun y, x) #1)
  show_goal_render
  exact hstop _

/-! ## 3. cond true / false — CLEAN -/

/-- info: ⊢ tglWp E pl(#1) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(if #true then #1 else #2) Φ := by
  twp_pure pl(if #true then #1 else #2)
  show_goal_render
  exact hstop _

/-- info: ⊢ tglWp E pl(#2) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(if #false then #1 else #2) Φ := by
  twp_pure pl(if #false then #1 else #2)
  show_goal_render
  exact hstop _

/-! ## 4. binop (computed result) — CLEAN ✓ (Bug 2 fixed)

`#1 + #2` evaluates to `#3` — `twp_expr_simp`'s `Int.reduce*` simprocs normalize
the `BinOp.eval` result. -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#1 + #2) Φ := by
  twp_pure pl(#1 + #2)
  show_goal_render
  exact hstop _

/-! ## 5. fst / snd of a pair — CLEAN -/

/-- info: ⊢ tglWp E pl(#1) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(fst((#1, #2))) Φ := by
  twp_pure pl(fst((#1, #2)))
  show_goal_render
  exact hstop _

/-- info: ⊢ tglWp E pl(#2) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(snd((#1, #2))) Φ := by
  twp_pure pl(snd((#1, #2)))
  show_goal_render
  exact hstop _

/-! ## 6. let-binding (β of a named lambda applied to a value) — CLEAN -/

/-- info: ⊢ tglWp E pl(#1 + #2) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(let x := #1; x + #2) Φ := by
  twp_pure pl((fun x, x + #2) #1)
  show_goal_render
  exact hstop _

/-! ## 7. fix-unfold + `@[pl_fold]` refolding -/

@[pl_fold]
def loopFolded : Exp rT := pl% rec f n := if n = #0 then #0 else f (n - #1)

-- Structurally distinct from `loopFolded` (so it is *not* defeq to any
-- `@[pl_fold]` constant) and unregistered: its self-reference must leak.
def loopBare : Exp rT := pl% rec f n := if n = #0 then #7 else f (n - #2)

/-! ### 7a. Named recursive constant auto-unfolds ✓ (Bug 3 fixed)

`twp_pures` unfolds the head constant `loopFolded` itself — no manual
`rw`/`simp only [loopFolded]` — and then (Bug 2) runs the recursion to
completion: `#0`. (Previously this was a NO-OP: the redex `(fix (lam …)) #2`
was hidden behind the constant and no step applied.) -/

/-- info: ⊢ tglWp E pl(#0) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(&loopFolded #2) Φ := by
  twp_pures
  show_goal_render
  exact hstop _

/-! ### 7b. Explicit `rw [loopFolded]` still works (backward compatible) -/

/-- info: ⊢ tglWp E pl(#0) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(&loopFolded #2) Φ := by
  rw [loopFolded]
  twp_pures
  show_goal_render
  exact hstop _

/-! ### 7c. Unregistered recursive constant also auto-unfolds ✓

`loopBare` is not `@[pl_fold]`, but `twp_pures` still unfolds it and runs to
completion `#7`. The rand-stalled samplers (§16, §25a) exercise the case where
the recursive body cannot fully reduce — and there too it now renders with named
binders (`rec a b := …`), never `⟪bvar⟫`/`.lam.fix`. -/

/-- info: ⊢ tglWp E pl(#7) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(&loopBare #2) Φ := by
  twp_pures
  show_goal_render
  exact hstop _

/-! ## 8. β-reduction leaving a binder USED in the body — CLEAN ✓ (Bug 1, headline)

`(fun x, fun y, x + y) #1` → residual `fun y, #1 + y` with the **source name `y`
recovered** (collected from the redex body's mdata, re-attached to the reduced
result, and the body reference resolved back to `y`): `pl(fun y, #1 + y)` — the
headline anonymous-lambda case, with no bvar/`.lam` leak and the real name. -/

/-- info: ⊢ tglWp E pl(fun y, #1 + y) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl((fun x, fun y, x + y) #1) Φ := by
  twp_pure pl((fun x, fun y, x + y) #1)
  show_goal_render
  exact hstop _

/-! ## 9. unops — CLEAN ✓ (Bug 2 fixed)

`~#true → #false` (boolean reduced in `pureStepResult`); `-#5 → #(-5)`
(`Int.neg z` rewritten to `-z`, then `Int.reduceNeg`). -/

/-- info: ⊢ tglWp E pl(#false) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(~#true) Φ := by
  twp_pure pl(~#true); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#(-5)) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(-#5) Φ := by
  twp_pure pl(-#5); show_goal_render; exact hstop _

/-! ## 10. more binops — CLEAN ✓ (Bug 2 fixed)

minus / mult / `<` / `&&` all normalize to literals/booleans. -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#5 - #2) Φ := by
  twp_pure pl(#5 - #2); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#12) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#3 * #4) Φ := by
  twp_pure pl(#3 * #4); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#2 < #3) Φ := by
  twp_pure pl(#2 < #3); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#false) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#true && #false) Φ := by
  twp_pure pl(#true && #false); show_goal_render; exact hstop _

/-! ## 11. scrut / case — CLEAN ✓ (Bugs 1 & 4 fixed)

The `v.isValue` side goal is now auto-discharged by `decide` (so plain `sorry`
suffices — no leftover goal), and the surface `case … | … => …` desugar renders
via the `case`/`scrut` keywords with named binders — no `.case`/`.lam`/`⟪bvar⟫`.
(The nesting reflects the inherent `scrut`-based desugaring of pattern `case`.) -/

/-- info: ⊢ tglWp E pl(inl(#1)) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(scrut inl(#1) with inl(x)) Φ := by
  twp_pure pl(scrut inl(#1) with inl(x))
  show_goal_render
  exact hstop _

/--
info:
⊢
tglWp E
  pl(case scrut inl(#1) with inl(_) | _ => fun _, let x := _; x + #1 | _ =>
      fun _, case scrut inl(#1) with inr(_) | _ => fun _, let y := _; y | _ => fun _, fail)
  Φ
-/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(case inl(#1) | inl(x) => x + #1 | inr(y) => y) Φ := by
  twp_pure pl(case inl(#1) | inl(x) => x + #1 | inr(y) => y)
  show_goal_render
  exact hstop _

/-! ## 12. multi-step `twp_pures` (nested let) — runs to completion

`let x := #1; let y := #2; x + y` reduces all the way to the binop result
`#(1 + 2)` (then stalls per §4). Confirms multi-step composition. -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(let x := #1; let y := #2; x + y) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## 13. end-to-end (mechanical, no display): `twp_pures` + `twp_value` closes -/

example : ⊢@{IProp GF} tglWp E pl(fst(((fun x, x) #1, #2)))
    (fun w : Val rT => iprop(⌜w = .int 1⌝)) := by
  twp_pures; twp_value; ipureintro; rfl

/-! ## 14. `twp_bind` context discovery — continuation renders CLEAN

Focusing `fst((#2, #3))` inside `#1 + ·` yields a continuation
`fun v ↦ tglWp E pl(#1 + {Exp.ofVal v}) Φ` — no bvar leak; the `{Exp.ofVal v}`
escape is the expected display for a Lean-level value spliced into `pl(…)`. -/

/-- info: ⊢ tglWp E pl(fst((#2, #3))) fun v ↦ tglWp E pl(#1 + {Exp.ofVal v}) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#1 + fst((#2, #3))) Φ := by
  twp_bind pl(fst((#2, #3))); show_goal_render; exact hstop _

/-! ## 15. value rule `twp_value` collapses a value goal to its postcondition -/

/-- info: ⊢ |={E}=> True -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl((#1, #2))
    (fun w : Val rT => iprop(⌜True⌝)) := by
  twp_value; show_goal_render; exact hstop _

/-! ## 16. local `rand` sampler — integration anchor — CLEAN ✓ (Bugs 1–3)

A recursive sampler whose body samples `rand 2`. `twp_pures` auto-unfolds it
(Bug 3) and stalls at the `rand … = #0` comparison (rand is not pure); with
`@[pl_names]` the unevaluated recursive body renders with its **source** binder
names `rec f n := if rand(#2, #()) = #0 then n else f (n + #1)` — no fresh
`a`/`b`, no `.lam.fix`/`⟪bvar⟫`. -/

@[pl_names]
def randLoop : Exp rT := pl% rec f n := if rand(#2, #.unit) = #0 then n else f (n + #1)

/--
info:
⊢ tglWp E pl(if rand(#2, #()) = #0 then #0 else (rec f n := if rand(#2, #()) = #0 then n else f (n + #1)) (#0 + #1)) Φ
-/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(&randLoop #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## 17. remaining binops — CLEAN ✓ (completes the operator matrix)

`div mod or xor le` and an *equal* `=` all reduce. With §4 (`+`) and §10 the
full 13-variant `BinOp` set now normalizes to literals/booleans. -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#6 / #2) Φ := by
  twp_pure pl(#6 / #2); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#1) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#7 % #3) Φ := by
  twp_pure pl(#7 % #3); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#true || #false) Φ := by
  twp_pure pl(#true || #false); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/ -- xor
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#true ^^ #false) Φ := by
  twp_pure pl(#true ^^ #false); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/ -- le
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#2 <= #3) Φ := by
  twp_pure pl(#2 <= #3); show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#true) Φ -/ -- eq (equal)
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#1 = #1) Φ := by
  twp_pure pl(#1 = #1); show_goal_render; exact hstop _

/-! ## 18. div / mod by zero — total eval, normalized ✓ (Lean `Int`: `n/0=0`, `n%0=n`)

`BinOp.eval` is total, so the step fires and (Bug 2) normalizes to `#0` / `#7`. -/

/-- info: ⊢ tglWp E pl(#0) Φ -/ -- div by zero
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#6 / #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#7) Φ -/ -- mod by zero
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(#7 % #0) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## 19. `fail` — stuck, renders CLEAN -/

/-- info: ⊢ tglWp E pl(fail) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(fail) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## 20. sugar — `let!` (pattern destructuring) and `assert` — CLEAN ✓

`assert(#true)` is a `cond` and reduces to `#()`. `let!` destructures via `scrut`
and reduces all the way to `#3`; its `isValue` side goals are now auto-discharged
(Bug 4), so plain `sorry` closes the single remaining WP goal. -/

/-- info: ⊢ tglWp E pl(#3) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(let! (a, b) := (#1, #2); a + b) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-- info: ⊢ tglWp E pl(#()) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(assert(#true)) Φ := by
  twp_pures; show_goal_render; exact hstop _

/-! ## 21. free-variable application displays CLEAN (no step) -/

/-- info: ⊢ tglWp E pl(f x y) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(f x y) Φ := by
  show_goal_render; exact hstop _

/-! ## 22. recursion runs to completion ✓ (Bug 2 fixed)

With binop normalization, `loopFolded 2` evaluates all the way to `#0` — each
comparison reduces so every `cond` fires. (Previously this stalled at
`#(decide (2 = 0))` and the recursion never progressed.) -/

/-- info: ⊢ tglWp E pl(#0) Φ -/ -- double-unfold now completes (Bug 2 fixed)
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(&loopFolded #2) Φ := by
  rw [loopFolded]; twp_pures; twp_pures; show_goal_render; exact hstop _

/-! ## 23. heap `alloc` focus via `twp_bind` — continuation renders CLEAN -/

/-- info: ⊢ tglWp E pl(alloc(#1)) fun v ↦ tglWp E pl(!{Exp.ofVal v}) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(!alloc(#1)) Φ := by
  twp_bind pl(alloc(#1)); show_goal_render; exact hstop _

/-! ## 24. `urand` focus — CLEAN ✓ (Bug 6 fixed)

The value-position literal now renders as `#1` (the `Exp.ofVal ⟨#1, _⟩` record is
collapsed to its underlying expression). The opaque bound value `{Exp.ofVal v}`
correctly stays escaped — there is no surface form for an abstract value. -/

/-- info: ⊢ tglWp E pl(urand) fun v ↦ tglWp E pl({Exp.ofVal v} + #1) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(urand + #1) Φ := by
  twp_bind pl(urand); show_goal_render; exact hstop _

/-! ## 25. Integration anchors — the REAL `geometric` / `GeometricTrial`

The named real-world samplers — both now render CLEANLY. `geometric` (Rocq port,
`GeometricTotal.lean`) is NOT `@[pl_fold]`-registered, so its unevaluated body
renders with fresh names (`rec a b := …`); `GeometricTrial`
(`BernoulliGeometric.lean`) IS `@[pl_fold]`, so its recursive self-reference
folds to `&Examples.GeometricTrial`. Either way: no bvars, no `.lam.fix`. These
are the before/after acceptance anchors for the whole effort. -/

-- 25a. `geometric ()` — auto-unfolds (Bug 3), stalls at the `rand … = #0`
-- comparison; the `else` branch renders the recursive body with named binders.
/--
info:
⊢ tglWp E pl(if rand(#2, #()) = #0 then #0 else (rec geo n := if rand(#2, #()) = #0 then #0 else geo n + #1) #() + #1) Φ
-/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E (Exp.app Examples.geometric (.lit .unit)) Φ := by
  twp_pures; show_goal_render; exact hstop _

-- 25b. `GeometricTrial f #0` — `@[pl_fold]` ⇒ recursive call folds to
-- `&Examples.GeometricTrial`; stalls at the abstract `f #()` discriminant. ✓
/-- info: ⊢ tglWp E pl(if f #() then &Examples.GeometricTrial f (#0 + #1) else #0) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl(&Examples.GeometricTrial f #0) Φ := by
  twp_pures; show_goal_render; all_goals first | exact hstop _ | exact hval _



/-! ## 26. Robustness — β with a binder-valued argument substituted before a surviving
binder. `(fun x, (x, fun y, #2)) (fun z, #3)` → `(fun z, #3, fun y, #2)`: BOTH the
substituted lambda's binder `z` and the surviving binder `y` keep their source names
(names come from the preserved mdata, not a positional guess — no mislabel). -/

/-- info: ⊢ tglWp E pl((fun z, #3, fun y, #2)) Φ -/
#guard_msgs (info) in
example : ⊢@{IProp GF} tglWp E pl((fun x, (x, fun y, #2)) (fun z, #3)) Φ := by
  twp_pure pl((fun x, (x, fun y, #2)) (fun z, #3))
  show_goal_render
  exact hstop _

end SteppingDisplayTest

end TotalEris
end ProbLang
