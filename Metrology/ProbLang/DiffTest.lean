import Metrology.ProbLang.PureStep
import Metrology.ProbLang.Eval
import Metrology.ProbLang.Notation

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

local instance : MeasurableSpace Exp := ⊤
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Val := ⊤
local instance : MeasurableSpace Cfg := ⊤

/-! ## Infrastructure -/

/-- Build a `PureHeadStep e1 e2` from a proof that `HeadStep` always maps
    `⟨e1, σ⟩` to `dirac ⟨e2, σ⟩`. The `safe` field is derived automatically. -/
theorem PureHeadStep.of_det (e1 e2 : Exp)
    (hdet : ∀ σ, HeadStep ⟨e1, σ⟩ {⟨e2, σ⟩} = 1) :
    PureHeadStep e1 e2 := by
  refine ⟨fun σ => ⟨⟨e2, σ⟩, ?_⟩, hdet⟩
  have h1 := hdet σ; positivity

/-- One step followed by n steps gives n+1 steps. -/
theorem nsteps_succ_intro {r : α → α → Prop} {n : ℕ} {a c b : α}
    (h1 : r a c) (h2 : nsteps r n c b) : nsteps r (n + 1) a b :=
  ⟨c, h1, h2⟩

/-- A single deterministic head step at a fixed state `σ`.
    Weaker than `PureHeadStep` (which requires all states); useful when
    the next expression may depend on `σ` (e.g. heap operations). -/
structure DetHeadStep (cfg1 cfg2 : Cfg) : Prop where
  safe : ∃ ρ : Cfg, HeadStep cfg1 {ρ} > 0
  det  : HeadStep cfg1 {cfg2} = 1

structure DetStep (cfg1 cfg2 : Cfg) : Prop where
  safe : ∃ ρ : Cfg, PrimStep cfg1 {ρ} > 0
  det  : PrimStep cfg1 {cfg2} = 1

theorem DetHeadStep.toDetStep {cfg1 cfg2 : Cfg} (h : DetHeadStep cfg1 cfg2) : DetStep cfg1 cfg2 := by
  constructor
  · obtain ⟨ρ, hρ⟩ := h.safe
    exact ⟨ρ, head_prim_step hρ⟩
  · obtain ⟨e1, σ1⟩ := cfg1
    rw [head_prim_step_eq h.safe]
    exact h.det

class DetExec (n : ℕ) (cfg1 cfg2 : Cfg) : Prop where
  det_exec : nsteps DetStep n cfg1 cfg2

theorem DetExec.succ {cfg1 cfg2 cfg3 : Cfg} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) [hrest : DetExec n cfg2 cfg3] :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

/-! ## ToExpr instances for reflection -/

open Lean in deriving instance ToExpr for Binder
open Lean in deriving instance ToExpr for BaseLit
open Lean in deriving instance ToExpr for UnOp
open Lean in deriving instance ToExpr for BinOp
open Lean in deriving instance ToExpr for Exp

open Lean in
instance : ToExpr Val where
  toTypeExpr := mkConst ``Val
  toExpr v :=
    let e := toExpr v.1
    -- Val.ofValueB e rfl : Val, where rfl : e.isValueB = true
    -- (kernel reduces isValueB on concrete e to Bool.true)
    let rfl_ := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool)
                        (mkApp (mkConst ``Exp.isValueB) e)
    mkApp2 (mkConst ``Val.ofValueB) e rfl_

open Lean in deriving instance ToExpr for EctxItem

/-! ## Symbolic execution tactic -/

theorem DetHeadStep.fst_pair {e1 e2 : Exp} (h1 : e1.isValueB = true) (h2 : e2.isValueB = true) (σ : State) :
    DetHeadStep ⟨.fst (.pair e1 e2), σ⟩ ⟨e1, σ⟩ := by
  have hv1 := e1.isValueB_iff.mp h1
  have hv2 := e2.isValueB_iff.mp h2
  exact ⟨⟨⟨e1, σ⟩, by simp [HeadStep, Exp.isValM_some hv1, Exp.isValM_some hv2]⟩,
         by simp [HeadStep, Exp.isValM_some hv1, Exp.isValM_some hv2]⟩

open Lean Meta in
-- Returns a proof of `e.isValueB = true`, or none if not a value.
private def isValueBPf (e : Expr) : MetaM (Option Expr) := do
  let r ← reduce (mkApp (mkConst ``Exp.isValueB) e)
  if r == mkConst ``Bool.true then
    return some (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) r)
  else
    return none

open Lean Lean.Elab Term Meta in
-- Given a concrete head-reducible cfg1, produce a proof of `DetHeadStep cfg1 ?cfg2`.
def elabDetHeadStep (cfg1 : Expr) : TermElabM Expr := do
  let .app (.app _ expr) state ← whnf cfg1 | throwError "elabDetHeadStep: cfg1 is not a Cfg"
  match ← whnf expr with
  | .app (.const ``Exp.fst _) arg =>
    match ← whnf arg with
    | .app (.app (.const ``Exp.pair _) e1) e2 =>
      let some h1 ← isValueBPf e1 | throwError "elabDetHeadStep: fst: e1 is not a value"
      let some h2 ← isValueBPf e2 | throwError "elabDetHeadStep: fst: e2 is not a value"
      return mkApp5 (mkConst ``DetHeadStep.fst_pair) e1 e2 h1 h2 state
    | _ => throwError "elabDetHeadStep: fst argument is not a pair"
  | e => throwError "elabDetHeadStep: no matching case for {e}"

/-- Lift a `DetHeadStep` through an evaluation context to a `DetStep`. -/
theorem DetHeadStep.toDetStep_fill (K : Ectx) {cfg1 cfg2 : Cfg}
    (h : DetHeadStep cfg1 cfg2) :
    DetStep ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ where
  safe := ⟨⟨K.fill cfg2.expr, cfg2.state⟩,
    fill_step (head_prim_step (by have := h.det; positivity))⟩
  det := by
    have hv := val_head_stuck (by have := h.det; positivity)
    rw [← fill_prim_step hv, head_prim_step_eq h.safe]
    exact h.det

open Lean Lean.Elab Term Meta in
-- Given a concrete cfg1, decompose it, find a DetHeadStep for the redex,
-- and lift to a DetStep via the evaluation context.
unsafe def elabDetStep (cfg1 : Expr) : TermElabM Expr := do
  let .app (.app _ expr) state ← whnf cfg1 | throwError "elabDetStep: cfg1 is not a Cfg"
  -- Step 1: evaluate Exp.decomp to get (K, redex)
  let expVal ← evalExpr Exp (mkConst ``Exp) expr
  let (kVal, redexVal) := expVal.decomp
  let K := toExpr kVal
  let redex := toExpr redexVal
  -- Step 2: find a DetHeadStep for the redex
  let headCfg := mkApp2 (mkConst ``Cfg.mk) redex state
  let headStep ← elabDetHeadStep headCfg
  -- Step 3: lift through K via toDetStep_fill
  let headStepType ← inferType headStep
  let .app (.app _ _) cfg2 := headStepType
    | throwError "elabDetStep: unexpected DetHeadStep type"
  return mkApp3 (mkConst ``DetHeadStep.toDetStep_fill) K headCfg cfg2 |>.app headStep

/-! ## Pure-step tactic (TODO: under construction) -/

-- open Lean Lean.Elab Tactic Meta in
-- def dischargeHeadStep : TacticM Unit := do
--   evalTactic (← `(tactic|
--     simp only [HeadStep, Exp.isValM, Exp.toVal?, Exp.isValue,
--                Exp.asValM, Option.unwrapM, BinOp.eval, UnOp.eval,
--                Exp.subst, Exp.subst']))
--   evalTactic (← `(tactic| simp only [Pi.single_apply, ite_eq_left_iff, not_and]))
--   evalTactic (← `(tactic| intro heq; exact absurd rfl heq))
--
-- open Lean Lean.Elab Tactic in
-- partial def pureStepsTac : TacticM Unit := do
--   try evalTactic (← `(tactic| rfl)); return
--   catch _ => pure ()
--   evalTactic (← `(tactic| apply nsteps_succ_intro))
--   let goals ← getGoals
--   if goals.length < 2 then
--     throwError "pure_steps: expected ≥ 2 goals after apply nsteps_succ_intro"
--   let restGoal := goals[1]!
--   setGoals [goals[0]!]
--   evalTactic (← `(tactic| apply PureHeadStep.toPureStep))
--   evalTactic (← `(tactic| apply PureHeadStep.of_det))
--   evalTactic (← `(tactic| intro σ))
--   dischargeHeadStep
--   let leftover ← getGoals
--   if !leftover.isEmpty then do
--     let ty ← leftover[0]!.getType
--     throwError "pure_steps: HeadStep goal not closed; remaining: {ty}"
--   setGoals [restGoal]
--   pureStepsTac
--
-- open Lean Lean.Elab Tactic in
-- elab "pure_steps" : tactic => pureStepsTac

open Lean Lean.Elab Term Meta in
elab "det_step_of" t:term : term => do
  let cfg1 ← elabTerm t (some (mkConst ``Cfg))
  unsafe elabDetStep (← whnf cfg1)

-- `DetExec 0 cfg cfg` by reflexivity.
theorem DetExec.refl (cfg : Cfg) : DetExec 0 cfg cfg where
  det_exec := rfl

-- Non-instance version of DetExec.succ for use in meta-code.
theorem DetExec.cons {cfg1 cfg2 cfg3 : Cfg} {n : ℕ}
    (hstep : DetStep cfg1 cfg2) (hrest : DetExec n cfg2 cfg3) :
    DetExec (n + 1) cfg1 cfg3 where
  det_exec := ⟨cfg2, hstep, hrest.det_exec⟩

open Lean Lean.Elab Term Meta in
-- Given a concrete cfg1 and fuel, build a term of type `DetExec n cfg1 cfg2`
-- where n and cfg2 are synthesized. Tries up to `fuel` DetSteps; stops early
-- if elabDetStep fails (expression is stuck / a value).
unsafe def elabDetExec (fuel : ℕ) (cfg1 : Expr) : TermElabM Expr := do
  if fuel == 0 then
    return mkApp (mkConst ``DetExec.refl) cfg1
  -- Try one step; stop if cfg1 is stuck.
  let stepOpt ← observing? (elabDetStep cfg1)
  match stepOpt with
  | none => return mkApp (mkConst ``DetExec.refl) cfg1
  | some step =>
    -- step : DetStep cfg1 cfg2; extract cfg2 from its type.
    let stepType ← inferType step
    let .app (.app _ _) cfg2 := stepType
      | throwError "elabDetExec: unexpected DetStep type"
    -- Recurse for the remaining steps.
    let rest ← elabDetExec (fuel - 1) cfg2
    -- rest : DetExec n cfg2 cfg3; extract n and cfg3.
    let restType ← inferType rest
    -- restType = DetExec n cfg2 cfg3, laid out as
    --   @DetExec n cfg2 cfg3
    let args := restType.getAppArgs
    -- args[0] = n, args[1] = cfg2, args[2] = cfg3
    let n    := args[0]!
    let cfg3 := args[2]!
    -- Build DetExec.cons hstep rest : DetExec (n+1) cfg1 cfg3
    return mkApp6 (mkConst ``DetExec.cons) cfg1 cfg2 cfg3 n step rest

open Lean Lean.Elab Term Meta in
elab "det_exec_of" fuel:num t:term : term => do
  let cfg1 ← elabTerm t (some (mkConst ``Cfg))
  unsafe elabDetExec fuel.getNat (← whnf cfg1)

/-! ## Smoke tests -/

section Tests

section Correctness

-- fst (pair #1 #2) steps to #1
example : DetStep ⟨pl(fst((#1, #2))), default⟩ ⟨pl(#1), default⟩ :=
  det_step_of ⟨pl(fst((#1, #2))), default⟩

-- #1 + fst(#2, #3) steps to #1 + #2
example : DetStep ⟨pl(#1 + fst((#2, #3))), default⟩ ⟨pl(#1 + #2), default⟩ :=
  det_step_of ⟨pl(#1 + fst((#2, #3))), default⟩

end Correctness

section Synthesis

-- The elab synthesizes the successor cfg without it being stated a priori
example : ∃ cfg2, DetStep ⟨pl(#1 + fst((#2, #3))), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(#1 + fst((#2, #3))), default⟩⟩

end Synthesis

section DetExecTests

-- fst((#1, #2)) + fst((#3, #4)) takes two steps (one for each fst).
-- After step 1: #1 + fst((#3, #4)); after step 2: #1 + #3; then stuck (no binop rule yet).
-- With fuel=2 the elab fires exactly twice before getting stuck.
example : ∃ n cfg2, DetExec n ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 2 ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩⟩

end DetExecTests


end Tests
end ProbLang
end
