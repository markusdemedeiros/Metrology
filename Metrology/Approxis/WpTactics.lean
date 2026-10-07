module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Iris.SpecRules
public import Metrology.TotalEris.WpTactics
public meta import Metrology.TotalEris.WpTactics
public import Metrology.ProbLang.Syntax.Notation
public meta import Metrology.ProbLang.Syntax.Notation
public import Iris.ProofMode.ProofModeM
public import Iris.ProofMode.Tactics.Basic
public import Lean
public import Qq

/-!
# Elaborator-based `wp_*` / `tp_*` tactics for the Approxis `wp`

The Approxis analogue of `TotalEris/WpTactics.lean` (which targets `tglWp`), providing
the Rocq Approxis workhorse tactics:

* `wp_bind e` / `wp_pure` / `wp_pures` / `wp_value` — program-side stepping of a
  `wp E e Φ` goal, with the evaluation context discovered automatically;
* `tp_bind e` / `tp_pure` / `tp_pures` — spec-side stepping of the (unique) `⤇ e'`
  hypothesis via `step_pure`, again with automatic context discovery.

The generic evaluation-context engine (`extractEctxItem`, `findECtx`, `pureStepResult`,
`reduceExp`, `reattachNames`) is shared with `TotalEris/WpTactics.lean`; only the
goal-runner and the consumed lemmas differ.
-/

namespace ProbLang.ApproxisWpGS

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Meta Elab Tactic Qq Iris Iris.ProofMode ProbLang.TotalEris

/-! ## Context-lifted pure step (lemma consumed by `wp_pure`) -/

section
variable {rT : Type _} [LawfulProbLangℝ rT]
  {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

public theorem wp_pure_step_ctx (K : Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : Exp rT}
    [PureExec φ n e₁ e₂] (Hφ : φ) {E : CoPset} {Φ : Val rT → IProp GF} :
    wp E (K.fill e₂) Φ ⊢ wp E (K.fill e₁) Φ := by
  have : PureExec φ n (K.fill e₁) (K.fill e₂) := PureExec.fill K
  exact (BI.laterN_intro n).trans (wp_pure_step_later' Hφ)

end

/-- `step_pure` with both endpoints anchored by (definitional) equalities, so `tp_pure`
can state the premise and conclusion in the exact syntactic form of the `⤇` hypothesis
rather than as an unreduced `Ectx.fill`. -/
public theorem step_pure_at {rT : Type _} [LawfulProbLangℝ rT] {GF : BundledGFunctors}
    {hlc : HasLC} [InvGS_gen hlc GF] [SpecGS rT GF] {E : CoPset}
    {e₁full e₂full e e' : Exp rT} (K : Ectx rT) {φ : Prop} {n : ℕ}
    (h₁ : e₁full = K.fill e) (h₂ : e₂full = K.fill e') (Hφ : φ) [PureExec φ n e e'] :
    ⤇ e₁full ⊢@{IProp GF} specUpdate rT E (⤇ e₂full) := by
  subst h₁ h₂
  exact step_pure K Hφ

/-- Reshape a `⤇` hypothesis along a (definitional) expression equality; `tp_bind` uses
it with `e₂ := Ectx.fill K e` and a `rfl` anchor. -/
public theorem specProgFrag_reshape {rT : Type _} [LawfulProbLangℝ rT]
    {GF : BundledGFunctors} [SpecGS rT GF] {e₁ e₂ : Exp rT} (h : e₁ = e₂) :
    (⤇ e₁) ⊢@{IProp GF} (⤇ e₂) := h ▸ .rfl

section PureStepsConsumers

variable {rT : Type _} [LawfulProbLangℝ rT] {GF : BundledGFunctors}

/-- Consume a `PureSteps` fact (a pure library computation, proved once by Lean
induction) on the program side. -/
public theorem wp_pure_steps [ApproxisWpGS (rT := rT) GF] {E : CoPset} {e₁ e₂ : Exp rT}
    {Φ : Val rT → IProp GF} (h : PureSteps e₁ e₂) :
    wp E e₂ Φ ⊢ wp E e₁ Φ :=
  have := h.pureExec
  (BI.laterN_intro _).trans (wp_pure_step_later' trivial)

/-- `wp_pure_steps` with the source endpoint anchored by a (definitional) equality, so
it applies to a goal whose expression is a raw β-residual of the library form. -/
public theorem wp_pure_steps_at [ApproxisWpGS (rT := rT) GF] {E : CoPset}
    {e₁ e₁' e₂ : Exp rT} {Φ : Val rT → IProp GF} (heq : e₁ = e₁') (h : PureSteps e₁' e₂) :
    wp E e₂ Φ ⊢ wp E e₁ Φ :=
  heq ▸ wp_pure_steps h

/-- Consume a `PureSteps` fact on the spec side, with both endpoints anchored by
(definitional) equalities so it applies to a `⤇` hypothesis syntactically. -/
public theorem step_pure_steps_at {hlc : HasLC} [InvGS_gen hlc GF] [SpecGS rT GF]
    {E : CoPset} {e₁full e₂full e e' : Exp rT} (K : Ectx rT)
    (h₁ : e₁full = K.fill e) (h₂ : e₂full = K.fill e') (h : PureSteps e e') :
    ⤇ e₁full ⊢@{IProp GF} specUpdate rT E (⤇ e₂full) := by
  subst h₁ h₂
  have := h.pureExec
  exact step_pure K trivial

/-- `step_alloc` with the allocated value anchored by a (definitional) equality, so the
resulting points-to reads in the caller's canonical form (e.g. `assocVal []` rather than
a raw `Val.mk`). -/
public theorem step_alloc_at {hlc : HasLC} [InvGS_gen hlc GF] [SpecGS rT GF] {E : CoPset}
    (K : Ectx rT) {v : Exp rT} (hv : IsVal v) {vv : Val rT} (hvv : vv = ⟨v, hv, hv.lc⟩) :
    ⤇ (K.fill (.alloc v)) ⊢@{IProp GF}
      specUpdate rT E iprop(∃ (l : Loc), (⤇ (K.fill pl(#(.loc l)))) ∗ (l ↦ₛ vv)) := by
  subst hvv
  exact step_alloc K hv

end PureStepsConsumers

/-! ## WP-goal runner

Destructures an iris proof-mode goal `ehyps ⊢ wp E e Φ` into its typed components.
The `wp` application spine is read positionally (`E`, `e`, `Φ` are its last three
arguments), so the runner is robust to the exact instance-argument layout. -/

/-- A proof-mode goal whose conclusion is `wp E e Φ`. -/
meta structure WpGoal where
  {u : Level}
  {α : Q(Type)}
  instPL : Q(ProbLang.LawfulProbLangℝ $α)
  {GF : Q(BundledGFunctors.{0, 0, 0})}
  instWp : Q(ProbLang.ApproxisWpGS (rT := $α) $GF)
  /-- The full `wp` application, with `E`, `e`, `Φ` as the trailing arguments. -/
  wpApp : LeanExpr
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  E : Q(CoPset)
  e : Q(Exp $α)
  Φ : LeanExpr
  hu : QuotedLevelDefEq u 0
  hprop : $prop =Q IProp $GF
  hbi : $bi =Q UPred.instBIUPred

/-- Rebuild the goal's `wp` application with a new expression and postcondition. -/
meta def WpGoal.mkWp (g : WpGoal) (e : LeanExpr) (Φ : LeanExpr) : LeanExpr :=
  let args := g.wpApp.getAppArgs
  let args := args.set! (args.size - 2) e
  let args := args.set! (args.size - 1) Φ
  mkAppN g.wpApp.getAppFn args

/-- Run `k` against the current goal, requiring it to be `ehyps ⊢ wp E e Φ`. -/
meta def runTacticWp {β : Type} (k : MVarId → WpGoal → ProofModeM β) : TacticM β := do
  ProofModeM.runTactic `wp fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "the goal {goal} must be an `IProp` at universe level 0"
    let ~q(IProp $GF) := prop
      | throwError "the goal {goal} must be an `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "expected the BI of `IProp` to be `UPred.instBIUPred`"
    let goalE : LeanExpr := (← instantiateMVars goal).consumeMData
    unless goalE.getAppFn.consumeMData.isConstOf ``ProbLang.ApproxisWpGS.wp do
      throwError "the goal {goal} must be a `wp`"
    let args := goalE.getAppArgs
    unless args.size == 7 do
      throwError "unexpected `wp` arity ({args.size}) in goal {goal}"
    have α : Q(Type) := args[0]!
    have instPL : Q(ProbLang.LawfulProbLangℝ $α) := args[1]!
    have instWp : Q(ProbLang.ApproxisWpGS (rT := $α) $GF) := args[3]!
    have E : Q(CoPset) := args[4]!
    have e : Q(Exp $α) := args[5]!
    let Φ : LeanExpr := args[6]!
    k mvar { instPL, GF, instWp, wpApp := goalE, hyps, E, e, Φ,
             hu := ⟨⟩, hprop := ⟨⟩, hbi := ⟨⟩ }

/-! ## `wp_bind` — focus on a subexpression by auto-discovering its context -/

/-- `wp_bind e` rebases the goal `wp E (K.fill e) Φ` to
`wp E e (fun v => wp E (K.fill v) Φ)`, discovering `K` automatically. -/
elab "wp_bind" colGt ppSpace focus:term:max : tactic =>
  runTacticWp fun mvar g => do
    let { α, instPL, GF, instWp, hyps, e, .. } := g
    let focus ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some res ← findECtx e (fun e => do guard (← isDefEq e focus))
      | throwTacticEx `wp_bind mvar
          m!"cannot unify {← ppExpr focus} with any evaluation context of {← ppExpr e}"
    have K : Q(Ectx $α) := res.K
    have e' : Q(Exp $α) := focus
    -- Continuation `fun v => wp E (K.fill (ofVal v)) Φ`, with `K` filled at the meta
    -- level so the continuation displays the clean refocused expression.
    let Φc : LeanExpr ←
      withLocalDeclDQ `v q(Val $α) fun v => do
        let body : Q(Exp $α) ← fill K q(Exp.ofVal $v)
        mkLambdaFVars #[v] (g.mkWp body g.Φ)
    have newGoal : Q(IProp $GF) := g.mkWp e' Φc
    let pf ← addBIGoal hyps newGoal
    let bindPf ← mkAppOptM ``ProbLang.ApproxisWpGS.wp_bind
      #[some α, some instPL, some GF, some instWp, some K, some g.E, some e', some g.Φ]
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, bindPf]
    mvar.assign transPf

/-! ## `wp_pure` — take a pure step at a redex, auto-discovering its context -/

/-- `wp_pure_core e?` takes a single `PureExec` reduction step at a redex of the goal's
expression, discovering the surrounding evaluation context automatically. The side
condition `φ` is discharged by `is_value` if trivial, else left as a goal. -/
elab "wp_pure_core" focus:(ppSpace colGt term:max)? : tactic =>
  runTacticWp fun mvar g => do
    let { α, instPL, GF, instWp, hyps, e, .. } := g
    let focusE? : Option Q(Exp $α) ← focus.mapM fun f => elabTermEnsuringTypeQ f q(Exp $α)
    let some res ← findECtx e fun e₁ => do
      if let some focusE := focusE? then guard (← isDefEq e₁ focusE)
      let some (e₁', e₂syn, names) ← pureStepResult instPL e₁ | failure
      let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
      let n : Q(Nat) ← mkFreshExprMVarQ q(Nat)
      let some inst ← ProofModeM.trySynthInstanceQ q(ProbLang.PureExec $φ $n $e₁' $e₂syn)
        | failure
      return ({ e₁ := e₁', e₂syn, names, φ, n, inst } : PureStepAt α instPL)
      | throwTacticEx `wp_pure mvar m!"no pure step applies"
    have K : Q(Ectx $α) := res.K
    let step := res.result
    let φ : Q(Prop) ← instantiateMVars step.φ
    let n : Q(Nat) ← instantiateMVars step.n
    let e₁ : Q(Exp $α) ← instantiateMVars step.e₁
    let e₂syn : Q(Exp $α) ← instantiateMVars step.e₂syn
    let e₂ : Q(Exp $α) ← do
      let cleaned ← reduceExp e₂syn
      if step.names.isEmpty then pure cleaned
      else pure (← reattachNames step.names 0 cleaned).1
    let inner : Q(Exp $α) ← fill K e₂
    have newGoal : Q(IProp $GF) := g.mkWp inner g.Φ
    let pf ← addBIGoal hyps newGoal
    let HΦ : Q($φ) ← mkFreshExprSyntheticOpaqueMVar q($φ)
    let gs ← Tactic.evalTacticAt (← `(tactic| (try is_value))) HΦ.mvarId!
    gs.forM addMVarGoal
    let stepPf ← mkAppOptM ``ProbLang.ApproxisWpGS.wp_pure_step_ctx
      #[some α, some instPL, some GF, some instWp, some K, some φ, some n,
        some e₁, some e₂, some step.inst, some HΦ, some g.E, some g.Φ]
    let transPf ← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, stepPf]
    mvar.assign transPf

/-- `wp_pure [e]` takes one pure step (plus display cleanup). -/
macro "wp_pure" focus:(ppSpace colGt term:max)? : tactic =>
  `(tactic| (wp_pure_core $[$focus]?; try simp only [pl_step_simp]))

/-- `wp_pure n` takes exactly `n` pure steps — for stopping at an abstraction
boundary (e.g. before an inlined library call) that `wp_pures` would step through. -/
macro "wp_pure " n:num : tactic =>
  `(tactic| iterate $n (wp_pure_core; try simp only [pl_step_simp]))

/-- `wp_pures` repeatedly takes pure steps until none apply. -/
macro "wp_pures" : tactic =>
  `(tactic| ((repeat (wp_pure_core; try simp only [pl_step_simp]));
             try simp only [pl_step_simp]))

/-! ## `wp_value` — discharge a value WP -/

/-- `wp_value` reduces a goal `wp E v Φ` (with `v` a value) to `Φ v`
(or `|={E}=> Φ v` if the postcondition cannot absorb the update). -/
elab "wp_value" : tactic =>
  runTacticWp fun mvar g => do
    let { α, instPL, GF, instWp, hyps, E, e, .. } := g
    -- Fast path: an `Exp.ofVal v` head is a value with a *lemma* witness — the
    -- computational `toVal?` may be stuck on an abstract `v`.
    let e0 : Q(Exp $α) ← pure e.consumeMData
    let (v, hproof) ← show ProofModeM (Q(Val $α) × LeanExpr) from
      match e0 with
      | ~q(Exp.ofVal $v) => return (v, q(Exp.toVal?_ofVal $v))
      | ~q(Val.fst $v) => return (v, q(Exp.toVal?_ofVal $v))
      | _ => do
        -- A closure's value check goes through the kernel (`Exp.closedFunVal?`).
        let tv : Q(Option (Val $α)) ← match ← Exp.closedFunVal? α e with
          | some (some v) => have v : Q(Val $α) := v; pure q(some $v)
          | some none => pure q(none)
          | none => whnf q(Exp.toVal? $e)
        let ~q(some $v) := tv
          | throwTacticEx `wp_value mvar m!"{← ppExpr e} is not a value"
        let hproof : Q(Exp.toVal? $e = some $v) ← mkFreshExprSyntheticOpaqueMVar
          q(Exp.toVal? $e = some $v)
        (← Tactic.evalTacticAt (← `(tactic| kernel_rfl)) hproof.mvarId!).forM addMVarGoal
        return (v, hproof)
    have goal : Q(IProp $GF) := LeanExpr.headBeta (mkApp g.Φ v)
    -- If the postcondition can absorb a `|={E}=>`, leave the clean goal `Φ v`;
    -- otherwise hand back `|={E}=> Φ v`.
    let c : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let A' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
    let Q' : Q(IProp $GF) ← mkFreshExprMVarQ q(IProp $GF)
    let useNoFupd : Bool ←
      if (← ProofModeM.trySynthInstanceQ
            q(ElimModal $c false .out $p' iprop(|={$E}=> $goal) $A' $goal $Q')).isSome then
        pure (← observing? (iSolveSidecondition c)).isSome
      else pure false
    have target : Q(IProp $GF) := if useNoFupd then goal else q(iprop(|={$E}=> $goal))
    let valLemma := if useNoFupd then ``ProbLang.ApproxisWpGS.wp_value_of_toVal
      else ``ProbLang.ApproxisWpGS.wp_value_fupd_of_toVal
    let pf ← addBIGoal hyps target
    let valPf ← mkAppOptM valLemma
      #[some α, some instPL, some GF, some instWp, some E, some e, some v, some g.Φ,
        some hproof]
    mvar.assign (← mkAppM ``Iris.BI.BIBase.Entails.trans #[pf, valPf])

/-- `wp_value_of_toVal` with the expression anchored by a (definitional) equality:
closes a goal `wp E e Φ` where `e` is only *definitionally* a value (e.g. a β-residual
closure), leaving `Φ v`. -/
public theorem wp_value_eq {rT : Type _} [LawfulProbLangℝ rT] {GF : BundledGFunctors}
    [ApproxisWpGS (rT := rT) GF] {E : CoPset} (v : Val rT) {e : Exp rT}
    (heq : e = Exp.ofVal v) {Φ : Val rT → IProp GF} :
    Φ v ⊢ wp E e Φ :=
  heq ▸ wp_value_of_toVal (Exp.toVal?_ofVal v)

/-- Re-express a goal `wp E e Φ` along a (definitional) expression equality;
`wp_show` uses this to refold a stepped expression to its clean library form. -/
public theorem wp_expr_eq {rT : Type _} [LawfulProbLangℝ rT] {GF : BundledGFunctors}
    [ApproxisWpGS (rT := rT) GF] {E : CoPset} {e e' : Exp rT} (heq : e = e')
    {Φ : Val rT → IProp GF} : wp E e' Φ ⊢ wp E e Φ :=
  heq ▸ .rfl

/-- `wp_show e'` refolds the goal `wp E e Φ` to `wp E e' Φ` for `e'` definitionally
equal to `e` — e.g. to fold a stepped β-residual back to its named library form
(with clean binder metadata) before applying an induction hypothesis. -/
elab "wp_show" colGt ppSpace e':term : tactic => do
  let tac ← runTacticWp fun mvar g => do
    addMVarGoal mvar
    let eS ← Term.exprToSyntax (g.e : LeanExpr)
    `(tactic| iapply (wp_expr_eq (e := $eS) (e' := $e') (by kernel_rfl)))
  Tactic.evalTactic tac

/-- `wp_value_at v` closes a value goal `wp E e Φ` with `e` a β-residual only
definitionally equal to `Exp.ofVal v`, leaving `Φ v`. -/
elab "wp_value_at" colGt ppSpace v:term : tactic => do
  let tac ← runTacticWp fun mvar g => do
    addMVarGoal mvar
    let eS ← Term.exprToSyntax (g.e : LeanExpr)
    `(tactic| iapply (wp_value_eq (e := $eS) $v (by kernel_rfl)))
  Tactic.evalTactic tac

/-- `wp_alloc` with the expression anchored by a (definitional) equality. -/
public theorem wp_alloc_eq {rT : Type _} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    {GF : BundledGFunctors} {hlc : HasLC} [ApproxisGS rT hlc GF] {E : CoPset} (v : Val rT)
    {ea : Exp rT} (heq : ea = .alloc (Exp.ofVal v)) {Φ : Val rT → IProp GF} : iprop%
    (∀ l, appHeapFrag l v -∗ Φ (.loc l)) ⊢ wp E ea Φ :=
  heq ▸ wp_alloc

/-- `wp_alloc_at v` applies `wp_alloc` to a goal `wp E (alloc e) Φ` where `e` is only
definitionally `Exp.ofVal v`. -/
elab "wp_alloc_at" colGt ppSpace v:term : tactic => do
  let tac ← runTacticWp fun mvar g => do
    addMVarGoal mvar
    let eS ← Term.exprToSyntax (g.e : LeanExpr)
    `(tactic| iapply (wp_alloc_eq (ea := $eS) $v (by kernel_rfl)))
  Tactic.evalTactic tac

/-- `wp_steps h` consumes a `PureSteps` fact `h` against the goal `wp E e Φ`, anchoring
the source endpoint to the goal's expression (which may be a raw β-residual only
*definitionally* equal to `h`'s source). -/
elab "wp_steps" colGt ppSpace h:term : tactic => do
  let tac ← runTacticWp fun mvar g => do
    addMVarGoal mvar
    let eS ← Term.exprToSyntax (g.e : LeanExpr)
    `(tactic| iapply (wp_pure_steps_at (e₁ := $eS) (by kernel_rfl) $h))
  Tactic.evalTactic tac

/-! ## Spec-side stepping: `tp_bind` / `tp_pure` / `tp_pures`

These act on the (unique) `⤇ espec` hypothesis of the Iris context, discovering the
evaluation context inside `espec` automatically and driving `step_pure` through the
`ElimModal` instance for `specUpdate` around `wp`. Both re-bind the hypothesis under
its existing name. -/

/-- Locate the unique `⤇ _` (`specProgFrag`) hypothesis: its name and spec expression. -/
meta def findSpecHyp {β : Q(Type)} (g : WpGoal) : ProofModeM (Option (Name × Q(Exp $β))) := do
  let some (name, _, _, ty) ← g.hyps.findM? fun _ _ _ ty => do
      return ty.consumeMData.isAppOf ``specProgFrag
    | return none
  return some (name, ty.consumeMData.appArg!)

/-- Split a spec expression `Ectx.fill Kctx inner` (with `Kctx` containing an *abstract*
tail, as in a universally-quantified library lemma) into `(some Kabs, inner')`, peeling
any concrete frame prefix of `Kctx` into `inner'`. A fully concrete expression is
returned as `(none, ·)`. Discovery then proceeds on `inner'`, and rebuilt contexts
append the abstract tail. -/
meta partial def splitAbstractCtx {β : Q(Type)} (espec : Q(Exp $β)) :
    ProofModeM (Option Q(Ectx $β) × Q(Exp $β)) := do
  let e : Q(Exp $β) ← pure espec.consumeMData
  match e with
  | ~q(Ectx.fill $Kctx $inner) => peel Kctx inner
  | _ => return (none, espec)
where
  peel (Kctx : Q(Ectx $β)) (inner : Q(Exp $β)) :
      ProofModeM (Option Q(Ectx $β) × Q(Exp $β)) := do
    let KctxW : Q(Ectx $β) ← whnf Kctx
    match KctxW with
    | ~q(List.nil) => return (none, inner)
    | ~q($Ki :: $Krest) => peel Krest (← fillItem inner Ki)
    | _ => return (some KctxW, inner)

/-- `tp_pure_core` takes one pure step in the `⤇` hypothesis via `step_pure`. -/
elab "tp_pure_core" : tactic => do
  let tacSeq ← runTacticWp fun mvar g => do
    -- Only reading the goal here: re-register it so it survives the runner.
    addMVarGoal mvar
    let { α, instPL, .. } := g
    let some (hypName, espec) ← findSpecHyp (β := α) g
      | throwTacticEx `tp_pure mvar m!"no `⤇` hypothesis found"
    -- A library lemma's hypothesis has the shape `Ectx.fill K inner` with `K` abstract:
    -- discover on `inner` and append `K` to the found frames.
    let (Kabs?, especInner) ← splitAbstractCtx (β := α) espec
    -- A prior spec step may leave the hypothesis as an unreduced (concrete) `Ectx.fill`;
    -- expose the head constructor for discovery (anchors still use `espec` verbatim).
    let especW : Q(Exp $α) ← whnf especInner
    let some res ← findECtx especW fun e₁ => do
      let some (e₁', e₂syn, _) ← pureStepResult instPL e₁ | failure
      return (e₁', e₂syn)
      | throwTacticEx `tp_pure mvar m!"no pure step applies to the spec expression"
    have Kd : Q(Ectx $α) := res.K
    have K : Q(Ectx $α) := match Kabs? with
      | some Kabs => if Kd.isAppOf ``List.nil then Kabs else q($Kd ++ $Kabs)
      | none => Kd
    let (e₁, e₂syn) := res.result
    let e₂ : Q(Exp $α) ← reduceExp e₂syn
    let e₂inner : Q(Exp $α) ← fill Kd e₂
    have e₂full : Q(Exp $α) := match Kabs? with
      | some Kabs => q(Ectx.fill $Kabs $e₂inner)
      | none => e₂inner
    let Ks ← Term.exprToSyntax K
    let e₁s ← Term.exprToSyntax e₁
    -- `e'` must be passed in synthesis form (`Exp.open' …`) for the `PureExec`
    -- instance to be found; the anchored `e₂full` carries the reduced display form.
    let e₂s ← Term.exprToSyntax e₂syn
    let especS ← Term.exprToSyntax espec
    let e₂fullS ← Term.exprToSyntax e₂full
    let hypIdent := mkIdent hypName
    `(tactic| imod (step_pure_at (K := $Ks) (e := $e₁s) (e' := $e₂s)
        (e₁full := $especS) (e₂full := $e₂fullS) (by kernel_rfl) (by kernel_rfl) (by is_value))
        $$ $hypIdent:ident with $hypIdent:ident)
  Tactic.evalTactic tacSeq

/-- `tp_pure` takes one pure step in the `⤇` hypothesis. The trailing
`simp only [pl_step_simp]` propositionally erases the stuck `openRec`/`closeRec`
wrappers the step's substitution leaves on opaque leaves (abstract values, closed
library constants) — without it they accumulate and every later step re-`whnf`s them. -/
macro "tp_pure" : tactic =>
  `(tactic| (tp_pure_core; try simp only [pl_step_simp]))

/-- `tp_pures` repeatedly takes pure steps in the `⤇` hypothesis until none apply. -/
macro "tp_pures" : tactic =>
  `(tactic| ((repeat (tp_pure_core; try simp only [pl_step_simp]));
             try simp only [pl_step_simp]))

/-- `tp_bind e` re-expresses the `⤇` hypothesis as `⤇ Ectx.fill K e` with `K` the
discovered context of `e`, so that spec-step lemmas (`step_load`, `step_store`, …)
apply by syntactic matching. -/
elab "tp_bind" colGt ppSpace focus:term:max : tactic => do
  let tacSeq ← runTacticWp fun mvar g => do
    addMVarGoal mvar
    let { α, .. } := g
    let focusE : Q(Exp $α) ← elabTermEnsuringTypeQ focus q(Exp $α)
    let some (hypName, espec) ← findSpecHyp (β := α) g
      | throwTacticEx `tp_bind mvar m!"no `⤇` hypothesis found"
    let (Kabs?, especInner) ← splitAbstractCtx (β := α) espec
    let especW : Q(Exp $α) ← whnf especInner
    let some res ← findECtx especW (fun e => do guard (← isDefEq e focusE))
      | throwTacticEx `tp_bind mvar
          m!"cannot unify {← ppExpr focusE} with any evaluation context of {← ppExpr espec}"
    have Kd : Q(Ectx $α) := res.K
    have K : Q(Ectx $α) := match Kabs? with
      | some Kabs => if Kd.isAppOf ``List.nil then Kabs else q($Kd ++ $Kabs)
      | none => Kd
    let Ks ← Term.exprToSyntax K
    -- Refocus on the user's `focus` term (defeq to the matched subterm), so the
    -- reshaped hypothesis reads in their clean form.
    let es ← Term.exprToSyntax (focusE : LeanExpr)
    let especS ← Term.exprToSyntax espec
    let hypIdent := mkIdent hypName
    `(tacticSeq|
      ihave $hypIdent:ident := specProgFrag_reshape
        (e₁ := $especS) (e₂ := Ectx.fill $Ks $es) (by kernel_rfl) $$ $hypIdent:ident)
  Tactic.evalTactic tacSeq

end ProbLang.ApproxisWpGS

