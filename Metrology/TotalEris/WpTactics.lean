module

public import Metrology.TotalEris.TotalLifting
public import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-!
# Elaborator-based `twp_*` tactics for `tglWp`

Port of iris-lean's `HeapLang/Tactic.lean` + `HeapLang/ProofMode.lean`,
specialised to ProbLang's `tglWp`. Unlike the previous macro layer (which
expanded to a single `iapply` and required the user to supply the evaluation
context `K` by hand), these are real `elab` tactics that:

* destructure the `tglWp E e Φ` goal once into a typed `TglWpGoal` (`runTacticTglWp`);
* mechanically decompose `e` into a list of `EctxItem`s and search for a redex
  matching a focus pattern (`extractEctxItem` / `findECtx`), so `twp_bind`/`twp_pure`
  never need an explicit `K`.

ProbLang has no language hierarchy, so we match the concrete `tglWp` head directly
rather than going through iris's `Wp`/`IrisGS_gen` abstractions.
-/

namespace ProbLang.TotalEris

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode

/-! ## Context-lifted pure step (lemma consumed by `twp_pure`)

`twp_pure_step_fupd` takes a bare `PureExec`; `twp_pure_step_ctx` lifts it through an
evaluation context `K` via `PureExec.fill`, so the tactic can step a redex in place.
Total WP has no `▷`, so there is no later-credit accounting to thread. -/

section
variable {rT : Type _} [ProbLang.ProbLangℝ rT] {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

public theorem ErisWpGS.twp_pure_step_ctx (K : Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : Exp rT}
    [PureExec φ n e₁ e₂] (Hφ : φ) {E : CoPset} {Φ : Val rT → IProp GF} :
    tglWp E (K.fill e₂) Φ ⊢@{IProp GF} tglWp E (K.fill e₁) Φ := by
  letI : PureExec φ n (K.fill e₁) (K.fill e₂) := PureExec.fill K
  exact twp_pure_step_fupd (n := n) φ Hφ

end

/-! ## Evaluation-context engine (mirrors `HeapLang/Tactic.lean`)

`extractEctxItem e` peels the outermost evaluation-context frame off `e`,
returning the frame and the sub-expression in its hole (mirrors
`Exp.decompItem`). `findECtx` searches the resulting frame stack for a
sub-expression satisfying a predicate. -/

/-- Peel one evaluation-context frame off `e`, returning the frame and the
sub-expression in its hole, or `(none, e)` if `e` is not decomposable. This *reflects*
ProbLang's `Exp.decompItem` (whnf + read off the result), so it uses the language's own
semantic value test (`toVal?`) rather than a syntactic `.ofVal` check — ProbLang values
are raw `.lit`/`.lam`/…, not `.ofVal`-wrapped as in HeapLang. -/
meta def extractEctxItem {α : Q(Type)} (e : Q(Exp $α)) :
    MetaM (Option Q(EctxItem $α) × Q(Exp $α)) := do
  let r : Q(Option (EctxItem $α × Exp $α)) ← whnf q(Exp.decompItem $e)
  match r with
  | ~q(some ($Ki, $e')) => return (some Ki, e')
  | _ => return (none, e)

/-- Fully decompose `e` into a frame stack `[innermost, …, outermost]` and the
innermost non-context sub-expression. The list order matches `Ectx.fill`
(`foldl (flip fillItem)`), so `Ectx.fill result.1 result.2 = e`. -/
meta partial def extractAllEctxItems {α : Q(Type)} (e : Q(Exp $α))
    (acc : List Q(EctxItem $α) := []) : MetaM (List Q(EctxItem $α) × Q(Exp $α)) := do
  match ← extractEctxItem e with
  | (some Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | (none, e) => return (acc, e)

/-- Plug `e` into a single frame `Ki` (mirrors `EctxItem.fillItem`). -/
meta def fillItem {α : Q(Type)} (e : Q(Exp $α)) : Q(EctxItem $α) → MetaM Q(Exp $α)
  | ~q(.appL $v₂)     => return q(.app $e (.ofVal $v₂))
  | ~q(.appR $e₁)     => return q(.app $e₁ $e)
  | ~q(.unop $op)     => return q(.unop $op $e)
  | ~q(.binopL $op $v₂) => return q(.binop $op $e (.ofVal $v₂))
  | ~q(.binopR $op $e₁) => return q(.binop $op $e₁ $e)
  | ~q(.condC $e₁ $e₂) => return q(.cond $e $e₁ $e₂)
  | ~q(.pairL $v₂)    => return q(.pair $e (.ofVal $v₂))
  | ~q(.pairR $e₁)    => return q(.pair $e₁ $e)
  | ~q(.fst)          => return q(.fst $e)
  | ~q(.snd)          => return q(.snd $e)
  | ~q(.inl)          => return q(.inl $e)
  | ~q(.inr)          => return q(.inr $e)
  | ~q(.case $e₁ $e₂) => return q(.case $e $e₁ $e₂)
  | ~q(.alloc)        => return q(.alloc $e)
  | ~q(.load)         => return q(.load $e)
  | ~q(.storeL $v₂)   => return q(.store $e (.ofVal $v₂))
  | ~q(.storeR $e₁)   => return q(.store $e₁ $e)
  | ~q(.tape)         => return q(.tape $e)
  | ~q(.randL $v₂)    => return q(.rand $e (.ofVal $v₂))
  | ~q(.randR $e₁)    => return q(.rand $e₁ $e)
  | ~q(.scrut $p)     => return q(.scrut $e $p)

/-- Quote a `List` of quoted `EctxItem`s as a quoted `Ectx`. -/
meta def quoteList {α : Q(Type)} : List Q(EctxItem $α) → Q(Ectx $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

/-- Plug `e` into the (quoted) context `K`, computing the filled expression at the meta
level. Result is defeq to `Ectx.fill K e` but β-reduced (no residual `Ectx.fill`). -/
meta partial def fill {α : Q(Type)} (K : Q(Ectx $α)) (e : Q(Exp $α)) : MetaM Q(Exp $α) :=
  match K with
  | ~q([]) => pure e
  | ~q($Ki :: $K') => do fill K' (← fillItem e Ki)

/-- A decomposition `e = Ectx.fill K e'` together with a result `a` computed at
the focus `e'`. -/
meta structure ECtxResultOf (α : Q(Type)) (β : Type) where
  result : β
  K : Q(Ectx $α)
  e' : Q(Exp $α)

/-- Walk the frame stack of `ogE` from innermost outward, returning the first
focus `e'` at which `pred e'` succeeds, together with the surrounding context. -/
meta partial def findECtx {α : Q(Type)} {β : Type} (ogE : Q(Exp $α))
    (pred : Q(Exp $α) → ProofModeM β) : ProofModeM (Option (ECtxResultOf α β)) := do
  let (Kis, inner) ← extractAllEctxItems ogE
  go inner Kis
where
  go (e : Q(Exp $α)) (Kis : List Q(EctxItem $α)) :
      ProofModeM (Option (ECtxResultOf α β)) := do
    if let some a ← observing? <| pred e then
      return some { result := a, K := quoteList Kis, e' := e }
    let Ki :: Kis' := Kis | return none
    go (← fillItem e Ki) Kis'

/-! ## WP-goal runner (mirrors `runTacticWp`)

Destructures an iris proof-mode goal `ehyps ⊢ tglWp E e Φ` into its typed
components. ProbLang has no language hierarchy, so we match the concrete
`ErisWpGS.tglWp` head directly. -/

/-- A proof-mode goal whose conclusion is `tglWp E e Φ`. -/
meta structure TglWpGoal where
  {u : Level}
  {α : Q(Type)}
  instPL : Q(ProbLang.ProbLangℝ $α)
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  instWp : Q(ErisWpGS (rT := $α) $GF)
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  E : Q(CoPset)
  e : Q(Exp $α)
  Φ : Q(Val $α → IProp $GF)
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

/-- Run `k` against the current goal, requiring it to be `ehyps ⊢ tglWp E e Φ`. -/
meta def runTacticTglWp {β : Type} (k : MVarId → TglWpGoal → ProofModeM β) : TacticM β := do
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "the goal {goal} must be an `IProp` at universe level 0"
    -- Binding `$GF` here refines `prop` to `IProp GF`, so `hyps`' carrier is concrete
    -- for `addBIGoal` downstream.
    let ~q(IProp $GF) := prop
      | throwError "the goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "expected the BI of `IProp` to be `UPred.instBIUPred`"
    -- Extract the `tglWp` arguments structurally (`tglWp` is `@[reducible]`, so a
    -- typed `~q` match against `$prop` does not refine; read the application spine).
    let goalE : LeanExpr := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.consumeMData.isConstOf ``ProbLang.TotalEris.ErisWpGS.tglWp do
      throwError "the goal {goal} must be a `tglWp`"
    let args := goalE.getAppArgs
    unless args.size == 7 do
      throwError "unexpected `tglWp` arity ({args.size}) in goal {goal}"
    have α : Q(Type) := args[0]!
    have instPL : Q(ProbLang.ProbLangℝ $α) := args[1]!
    have instWp : Q(ErisWpGS (rT := $α) $GF) := args[3]!
    have E : Q(CoPset) := args[4]!
    have e : Q(Exp $α) := args[5]!
    have Φ : Q(Val $α → IProp $GF) := args[6]!
    k mvar { instPL, instWp, hyps, E, e, Φ, hu := ⟨⟩, hprop := ⟨⟩, hbi := ⟨⟩ }

/-! ## `twp_bind` — focus on a subexpression by auto-discovering its context -/

/-- `twp_bind e` rebases the goal `tglWp E (K.fill e) Φ` to `tglWp E e (…)`, with
the evaluation context `K` discovered automatically (no manual `K`). -/
elab "twp_bind" colGt ppSpace focus:term:max : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let focus ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some res ← findECtx e (fun e => do guard (← isDefEq e focus))
      | throwTacticEx `twp_bind mvar
          m!"cannot unify {← ppExpr focus} with any evaluation context of {← ppExpr e}"
    have K : Q(Ectx $α) := res.K
    have e' : Q(Exp $α) := res.e'
    -- Φ' v := tglWp E (K.fill (ofVal v)) Φ, with `K` filled at the meta level so the
    -- continuation shows the clean refocused expression (defeq to `Ectx.fill K (ofVal v)`).
    let Φc : Q(Val $α → IProp $GF) ←
      withLocalDeclDQ `v q(Val $α) fun v => do
        let body : Q(Exp $α) ← fill K q(Exp.ofVal $v)
        mkLambdaFVars #[v]
          q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $body $Φ)
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $e' $Φc)
    -- Build the proof with raw `mkApp*` rather than `q(…)`: `tglWp` is
    -- `@[reducible, expose]`, so quoting `tglWp_bind`'s statement makes Qq `whnf` it
    -- into `bi_least_fixpoint` at elaboration time (heartbeat blow-up). `mkAppOptM`
    -- type-checks lazily and avoids that.
    let bindPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.tglWp_bind
      (#[α, instPL, GF, instWp, K, E, e', Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, bindPf]
    mvar.assign transPf

/-- Symbolic result of one pure step at a redex head, mirroring the `PureExec` instances.
For syntactic-result redexes (beta, fix, cond, fst/snd, case) it returns the stepped
expression *unreduced* (e.g. `open' body v`). For computed-result redexes (`binop`,
`unop`, `scrut`) it reduces the corresponding evaluator (`BinOp.eval`/`UnOp.eval`/
`Pat.tryMatch`) via `whnf` and reads off the result, returning `none` if the evaluator is
stuck (operands not concrete). `PureExec` synthesis then confirms the step and
`twp_expr_simp` cleans up. -/
meta def pureStepResult {α : Q(Type)} (instPL : Q(ProbLang.ProbLangℝ $α)) :
    Q(Exp $α) → MetaM (Option Q(Exp $α))
  | ~q(.app (.lam $body) $v)              => return some q(Exp.open' $body $v)
  | ~q(.app (.fix $body) $v)              => return some q(Exp.app (Exp.open' $body (.fix $body)) $v)
  | ~q(.cond (.lit (.bool true)) $et $ef) => return some et
  | ~q(.cond (.lit (.bool false)) $et $ef)=> return some ef
  | ~q(.fst (.pair $e1 $_e2))             => return some e1
  | ~q(.snd (.pair $_e1 $e2))             => return some e2
  | ~q(.case (.inl $v) $el $_er)          => return some q(Exp.app $el $v)
  | ~q(.case (.inr $v) $_el $er)          => return some q(Exp.app $er $v)
  | ~q(.binop $op $e1 $e2)                => do
    let r : Q(Option (Exp $α)) ← whnf q(@BinOp.eval $α $instPL $op $e1 $e2)
    match r with
    | ~q(some $res) => return some res
    | _             => return none
  | ~q(.unop $op $e1)                     => do
    let r : Q(Option (Exp $α)) ← whnf q(@UnOp.eval $α $op $e1)
    match r with
    | ~q(some $res) => return some res
    | _             => return none
  | ~q(.scrut $v $p)                      => do
    let r : Q(Option (Exp $α)) ← whnf q(@Pat.tryMatch $α $instPL $p $v)
    match r with
    | ~q(some $b) => return some q(Exp.inl $b)
    | ~q(none)    => return some q(Exp.inr (.lit .unit))
    | _           => return none
  | _                                     => return none

/-! ## `twp_pure` — take a pure step at a redex, auto-discovering its context -/

/-- `twp_pure_core e` takes a single pure (`PureExec`) reduction step at the redex `e`,
discovering the surrounding evaluation context `K` automatically. The pure-step side
condition `φ` (e.g. value-hood) is discharged if trivial, else left as a goal. Leaves the
stepped goal *unreduced*; `twp_pure` is the cleaning wrapper. -/
elab "twp_pure_core" focus:(ppSpace colGt term:max)? : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    -- Optional focus: with an argument, step that specific redex; without, step the
    -- first redex found while descending the evaluation context.
    let focusE? : Option Q(Exp $α) ← focus.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let some res ← findECtx e fun e₁ => do
      if let some focusE := focusE? then guard (← isDefEq e₁ focusE)
      let some e₂ ← pureStepResult instPL e₁ | failure
      let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
      let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
      let some inst ← ProofModeM.trySynthInstanceQ q(ProbLang.PureExec $φ $n $e₁ $e₂)
        | failure
      return (φ, n, e₂, inst)
      | throwTacticEx `twp_pure mvar m!"no pure step applies"
    have K : Q(Ectx $α) := res.K
    have e₁ : Q(Exp $α) := res.e'
    let φ : Q(Prop) ← instantiateMVars res.result.1
    let n : Q(Nat) ← instantiateMVars res.result.2.1
    let e₂ : Q(Exp $α) ← instantiateMVars res.result.2.2.1
    let inst : Q(ProbLang.PureExec $φ $n $e₁ $e₂) := res.result.2.2.2
    -- New goal: `tglWp E (K.fill e₂) Φ`, but with `K` filled at the meta level so the
    -- goal shows the clean stepped expression (not a `Ectx.fill` redex that would hide
    -- the next redex from `twp_pures`). Defeq to `Ectx.fill K e₂`.
    let inner : Q(Exp $α) ← fill K e₂
    let pf ← addBIGoal hyps
      q(@ProbLang.TotalEris.ErisWpGS.tglWp $α $instPL $GF $instWp $E $inner $Φ)
    -- Discharge the pure-step side condition (`True`, value-hood, …); leave it as a
    -- goal if non-trivial. Unlike `iSolveSidecondition`, this never throws.
    let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    let gs ← Tactic.evalTacticAt
      (← `(tactic| (try (first
            | trivial
            | repeat' (first
                | rfl | exact ⟨IsVal.lit⟩ | exact ⟨IsVal.lam⟩ | refine ⟨?_, ?_⟩)))))
      HΦ.mvarId!
    gs.forM addMVarGoal
    let stepPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.twp_pure_step_ctx
      (#[α, instPL, GF, instWp, K, φ, n, e₁, e₂, inst, HΦ, E, Φ].map some)
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, stepPf]
    mvar.assign transPf

/-! ## `twp_value` — discharge a value WP (semantic value head) -/

/-- `twp_value` closes a goal `tglWp E e Φ` when `e` is a value `v` (detected via
`e.toVal?`, so it works on raw `.lit`/`.lam`/… values, not just `Exp.ofVal v`),
reducing it to the postcondition `Φ v`. The TotalEris analogue of iris's
`wp_value_head`. -/
elab "twp_value" : tactic =>
  runTacticTglWp fun mvar { α, GF, instPL, instWp, hyps, E, e, Φ, .. } => do
    let tv : Q(Option (Val $α)) ← whnf q(Exp.toVal? $e)
    let ~q(some $v) := tv
      | throwTacticEx `twp_value mvar m!"{← ppExpr e} is not a value"
    -- `e.toVal? = some v` holds definitionally (`v` came from whnf of `e.toVal?`);
    -- discharge it with `rfl`.
    let hproof : Q(Exp.toVal? $e = some $v) ← mkFreshExprSyntheticOpaqueMVar
      q(Exp.toVal? $e = some $v)
    (← Tactic.evalTacticAt (← `(tactic| rfl)) hproof.mvarId!).forM addMVarGoal
    have goal : Q(IProp $GF) := Expr.headBeta q($Φ $v)
    -- iWpValueHead: if the postcondition can absorb a `|={E}=>` (an `ElimModal` exists
    -- whose side condition is dischargeable), leave the clean goal `Φ v`; otherwise hand
    -- back `|={E}=> Φ v` so the user can still update ghost state.
    let c : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let A' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
    let Q' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
    let useNoFupd : Bool ←
      if (← ProofModeM.trySynthInstanceQ
            q(ElimModal $c false $p' iprop(|={$E}=> $goal) $A' $goal $Q')).isSome then
        pure (← observing? (iSolveSidecondition c)).isSome
      else pure false
    if useNoFupd then
      let pf ← addBIGoal hyps goal
      let valPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.tglWp_value_of_toVal
        (#[α, instPL, GF, instWp, E, e, v, Φ, hproof].map some)
      mvar.assign (← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, valPf])
    else
      let pf ← addBIGoal hyps q(iprop(|={$E}=> $goal))
      let valPf ← mkAppOptM ``ProbLang.TotalEris.ErisWpGS.tglWp_value_fupd_of_toVal
        (#[α, instPL, GF, instWp, E, e, v, Φ, hproof].map some)
      mvar.assign (← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, valPf])

/-- `wp_value` — Rocq-facing alias for `twp_value`. -/
macro "wp_value" : tactic => `(tactic| twp_value)

/-! ## Cleanup + composite tactics -/

/-- `twp_expr_simp` reduces the substitutions left by a pure step (`open'`/`openRec`)
and the surrounding boolean/arithmetic redexes, recovering a clean WP goal. The
TotalEris analogue of iris's `wp_expr_simp` (named `twp_*` to avoid the clash with
iris-lean's HeapLang `wp_expr_simp`). -/
macro "twp_expr_simp" : tactic =>
  `(tactic| simp only [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      ↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, Nat.zero_add,
      Var.internal.injEq, reduceCtorEq])

/-- `twp_pure [e]` takes one pure step (`twp_pure_core`) and then cleans up the resulting
substitutions (`twp_expr_simp`), matching iris's auto-finishing `wp_pure`. -/
macro "twp_pure" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (twp_pure_core $[$focus]?; try twp_expr_simp))

/-- `twp_lam` β-reduces a `(λ. _) v` application — an alias for `twp_pure`. -/
macro "twp_lam" : tactic => `(tactic| twp_pure)

/-- `wp_lam` — Rocq-facing alias for `twp_lam`. -/
macro "wp_lam" : tactic => `(tactic| twp_lam)

/-- `twp_rec` unfolds a recursive call `(rec f x := e) v` — `twp_pure` already handles
the `app_fix` step, so this is an alias. -/
macro "twp_rec" : tactic => `(tactic| twp_pure)

/-- `twp_finish` cleans up after a step: reduce leftover substitutions, then close the
goal if it has become a value WP. The TotalEris analogue of iris's `wp_finish`. -/
macro "twp_finish" : tactic =>
  `(tactic| ((try twp_expr_simp); (try twp_value)))

/-- `twp_pures` repeatedly takes pure steps (cleaning up after each) until none apply. -/
macro "twp_pures" : tactic => `(tactic| repeat (twp_pure_core; try twp_expr_simp))

end ProbLang.TotalEris
