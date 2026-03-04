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

/-! ## Computable value check -/

def Exp.isValueB : Exp → Bool
  | .lit _ | .letrec _ _ _ => true
  | .inl e | .inr e => e.isValueB
  | .pair e1 e2 => e1.isValueB && e2.isValueB
  | _ => false

theorem Exp.isValueB_iff (e : Exp) : e.isValueB = true ↔ e.isValue := by
  induction e <;> simp_all [isValueB, isValue, Bool.and_eq_true]

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
-- Given a concrete cfg1, produce a proof of `DetStep cfg1 ?cfg2`,
-- unifying ?cfg2 with the successor configuration.
def elabDetStep (cfg1 : Expr) : TermElabM Expr := do
  let .app (.app _ expr) state ← whnf cfg1 | throwError "elabDetStep: cfg1 is not a Cfg"
  match ← whnf expr with
  | .app (.const ``Exp.fst _) arg =>
    match ← whnf arg with
    | .app (.app (.const ``Exp.pair _) e1) e2 =>
      let some h1 ← isValueBPf e1 | throwError "elabDetStep: fst: e1 is not a value"
      let some h2 ← isValueBPf e2 | throwError "elabDetStep: fst: e2 is not a value"
      let headStep := mkApp5 (mkConst ``DetHeadStep.fst_pair) e1 e2 h1 h2 state
      let cfg2 := mkApp2 (mkConst ``Cfg.mk) e1 state
      return mkApp3 (mkConst ``DetHeadStep.toDetStep) cfg1 cfg2 headStep
    | _ => throwError "elabDetStep: fst argument is not a pair"
  | e => throwError "elabDetStep: no matching case for {e}"

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
  elabDetStep cfg1

/-! ## Smoke tests -/

section Tests

-- fst (pair #1 #2): should hit "fst case not yet implemented"
#check (det_step_of ⟨.fst (.pair (.lit (.int 1)) (.lit (.int 2))), default⟩)

end Tests

/-! ## Smoke tests (TODO: restore once tactic works) -/

-- section Tests
--
-- -- 0 steps: value already
-- example : nsteps PureStep 0 (pl(#1)) (pl(#1)) := by pure_steps
--
-- -- 1 step: beta reduction  (fun x, x) #1 → #1
-- example : nsteps PureStep 1 (pl((fun x, x) #1)) (pl(#1)) := by pure_steps
--
-- -- 2 steps: (fun x, x + x) #1 → #1 + #1 → #2
-- example : nsteps PureStep 2 (pl((fun x, x + x) #1)) (pl(#2)) := by pure_steps
--
-- -- 3 steps: let x := #1; if (x = #1) then #42 else #0
-- example : nsteps PureStep 3
--     (pl(let x := #1; if (x = #1) then #42 else #0))
--     (pl(#42)) := by pure_steps
--
-- end Tests

end ProbLang
end
