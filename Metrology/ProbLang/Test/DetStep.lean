import Metrology.ProbLang.DetStep
import Metrology.ProbLang.Notation

namespace ProbLang

open Lean Meta Elab

/-! ## ToExpr instances for reflection -/
deriving instance ToExpr for BaseLit
deriving instance ToExpr for UnOp
deriving instance ToExpr for BinOp
deriving instance ToExpr for Ty
deriving instance ToExpr for Binder
deriving instance ToExpr for Annot
deriving instance ToExpr for Exp
deriving instance ToExpr for IsVal
instance : ToExpr Val where
  toTypeExpr := mkConst ``Val
  toExpr v := mkApp4 (mkConst ``Sigma.mk [.zero, .zero])
    (mkConst ``Exp) (mkConst ``IsVal) (toExpr v.1) (toExpr v.2)
deriving instance ToExpr for EctxItem

/-! ## Symbolic execution tactic -/

/-- Try to build an `IsVal e` witness by reducing `IsVal.check? e`. -/
private def mkIsValWitness (e : Expr) : MetaM (Option Expr) := do
  let check := mkApp (mkConst ``IsVal.check?) e
  let r ← reduce check
  match r with
  | .app (.app (.const ``Option.some _) _) w => return some w
  | _ => return none

open Term in
unsafe def elabDetHeadStep (cfg1 : Expr) : TermElabM Expr := do
  let .app (.app _ expr) state ← whnf cfg1 | throwError "elabDetHeadStep: cfg1 is not a Cfg"
  match ← whnf expr with
  | .app (.const ``Exp.fst _) arg =>
    match ← whnf arg with
    | .app (.app (.const ``Exp.pair _) e1) e2 =>
      let some h1 ← mkIsValWitness e1 | throwError "elabDetHeadStep: fst: e1 is not a value"
      let some h2 ← mkIsValWitness e2 | throwError "elabDetHeadStep: fst: e2 is not a value"
      return mkApp5 (mkConst ``DetHeadStep.fst_pair) e1 e2 h1 h2 state
    | _ => throwError "elabDetHeadStep: fst argument is not a pair"
  | .app (.const ``Exp.snd _) arg =>
    match ← whnf arg with
    | .app (.app (.const ``Exp.pair _) e1) e2 =>
      let some h1 ← mkIsValWitness e1 | throwError "elabDetHeadStep: snd: e1 is not a value"
      let some h2 ← mkIsValWitness e2 | throwError "elabDetHeadStep: snd: e2 is not a value"
      return mkApp5 (mkConst ``DetHeadStep.snd_pair) e1 e2 h1 h2 state
    | _ => throwError "elabDetHeadStep: snd argument is not a pair"
  | .app (.app (.const ``Exp.app _) fn) arg =>
    match ← whnf fn with
    | .app (.app (.app (.const ``Exp.letrec _) f) x) body =>
      let some hv ← mkIsValWitness arg | throwError "elabDetHeadStep: app: argument is not a value"
      -- @DetHeadStep.app_letrec f x body arg hv state
      return mkApp6 (mkConst ``DetHeadStep.app_letrec) f x body arg hv state
    | _ => throwError "elabDetHeadStep: app: function is not a letrec"
  | .app (.app (.const ``Exp.unop _) op) e =>
    let some hv ← mkIsValWitness e | throwError "elabDetHeadStep: unop: e is not a value"
    let opVal     ← evalExpr UnOp (mkConst ``UnOp) op
    let eVal      ← evalExpr Exp  (mkConst ``Exp)  e
    let some resultVal := UnOp.eval opVal eVal
      | throwError "elabDetHeadStep: unop: UnOp.eval returned none"
    let result := toExpr resultVal
    let optExpType := mkApp (mkConst ``Option [.zero]) (mkConst ``Exp)
    let heval := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optExpType
                         (mkApp2 (mkConst ``UnOp.eval) op e)
    -- @DetHeadStep.unop op e result hv heval state
    return mkApp6 (mkConst ``DetHeadStep.unop) op e result hv heval state
  | .app (.app (.app (.const ``Exp.binop _) op) e1) e2 =>
    let some h1 ← mkIsValWitness e1 | throwError "elabDetHeadStep: binop: e1 is not a value"
    let some h2 ← mkIsValWitness e2 | throwError "elabDetHeadStep: binop: e2 is not a value"
    -- Evaluate BinOp.eval op e1 e2 at meta-level using evalExpr
    let opVal  ← evalExpr BinOp (mkConst ``BinOp) op
    let e1Val  ← evalExpr Exp   (mkConst ``Exp)   e1
    let e2Val  ← evalExpr Exp   (mkConst ``Exp)   e2
    let some resultVal := BinOp.eval opVal e1Val e2Val
      | throwError "elabDetHeadStep: binop: BinOp.eval returned none"
    let result := toExpr resultVal
    let optExpType := mkApp (mkConst ``Option [.zero]) (mkConst ``Exp)
    let heval := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optExpType
                         (mkApp3 (mkConst ``BinOp.eval) op e1 e2)
    -- @DetHeadStep.binop op e1 e2 result h1 h2 heval state
    return mkApp8 (mkConst ``DetHeadStep.binop) op e1 e2 result h1 h2 heval state
  | .app (.app (.app (.const ``Exp.case _) scrut) el) er =>
    match ← whnf scrut with
    | .app (.const ``Exp.inl _) v =>
      let some hv ← mkIsValWitness v | throwError "elabDetHeadStep: case_inl: scrutinee is not a value"
      return mkApp5 (mkConst ``DetHeadStep.case_inl) v el er hv state
    | .app (.const ``Exp.inr _) v =>
      let some hv ← mkIsValWitness v | throwError "elabDetHeadStep: case_inr: scrutinee is not a value"
      return mkApp5 (mkConst ``DetHeadStep.case_inr) v el er hv state
    | _ => throwError "elabDetHeadStep: case: scrutinee is not inl/inr"
  | .app (.app (.app (.const ``Exp.cond _) cond_e) et) ef =>
    match ← whnf cond_e with
    | .app (.const ``Exp.lit _) (.app (.const ``BaseLit.bool _) (.const ``Bool.true _)) =>
      return mkApp3 (mkConst ``DetHeadStep.cond_true) et ef state
    | .app (.const ``Exp.lit _) (.app (.const ``BaseLit.bool _) (.const ``Bool.false _)) =>
      return mkApp3 (mkConst ``DetHeadStep.cond_false) et ef state
    | _ => throwError "elabDetHeadStep: cond: condition is not a boolean literal"
  | .app (.const ``Exp.alloc _) v =>
    let some hv ← mkIsValWitness v | throwError "elabDetHeadStep: alloc: argument is not a value"
    return mkApp3 (mkConst ``DetHeadStep.alloc) v hv state
  | .app (.const ``Exp.load _) addr =>
    match ← whnf addr with
    | .app (.const ``Exp.lit _) (.app (.const ``BaseLit.loc _) loc) =>
      let σVal   ← evalExpr State (mkConst ``State) state
      let locVal ← evalExpr Loc   (mkConst ``Loc)   loc
      let some vVal := σVal.heap[locVal]?
        | throwError "elabDetHeadStep: load: location not in heap"
      let v := toExpr vVal
            -- TODO: build hlookup : σ.heap[ℓ]? = some v
      let heapExpr := mkApp (mkConst ``State.heap) state
      let someV := mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Val) v
      let hlookupTy ← mkEq (← mkAppM ``getElem? #[heapExpr, loc]) someV
      let hlookup := mkApp2 (mkConst ``sorryAx [.zero]) hlookupTy (mkConst ``Bool.false)
      return mkApp4 (mkConst ``DetHeadStep.load) loc v state hlookup
    | _ => throwError "elabDetHeadStep: load: argument is not a location literal"
  | .app (.app (.const ``Exp.store _) addr) e =>
    match ← whnf addr with
    | .app (.const ``Exp.lit _) (.app (.const ``BaseLit.loc _) loc) =>
      let some hv ← mkIsValWitness e | throwError "elabDetHeadStep: store: value is not a value"
      let σVal   ← evalExpr State (mkConst ``State) state
      let locVal ← evalExpr Loc   (mkConst ``Loc)   loc
      let eVal   ← evalExpr Exp   (mkConst ``Exp)   e
      let some v_oldVal := σVal.heap[locVal]?
        | throwError "elabDetHeadStep: store: location not in heap"
      let some v_newVal := eVal.toVal?
        | throwError "elabDetHeadStep: store: expression not a value"
      let v_old := toExpr v_oldVal
      let v_new := toExpr v_newVal
      let hlookupTy ← mkEq (← mkAppM ``getElem? #[mkApp (mkConst ``State.heap) state, loc])
                            (mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Val) v_old)
      let hlookup := mkApp2 (mkConst ``sorryAx [.zero]) hlookupTy (mkConst ``Bool.false)
      let hnewTy ← mkEq (mkApp (mkConst ``Exp.toVal?) e)
                         (mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Val) v_new)
      let hnew := mkApp2 (mkConst ``sorryAx [.zero]) hnewTy (mkConst ``Bool.false)
      return mkApp8 (mkConst ``DetHeadStep.store) loc e v_old v_new hv state hlookup hnew
    | _ => throwError "elabDetHeadStep: store: address is not a location literal"
  | e => throwError "elabDetHeadStep: no matching case for {e}"

/-- Lift a `DetHeadStep` through an evaluation context to a `DetStep`. -/
theorem DetHeadStep.toDetStep_fill (K : Ectx) {cfg1 cfg2 : Cfg}
    (h : DetHeadStep cfg1 cfg2) :
    DetStep ⟨K.fill cfg1.expr, cfg1.state⟩ ⟨K.fill cfg2.expr, cfg2.state⟩ :=
  h.toDetStep.fill K

open Term in
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

open Term in
elab "det_step_of" t:term : term => do
  let cfg1 ← elabTerm t (some (mkConst ``Cfg))
  unsafe elabDetStep (← whnf cfg1)

open Term in
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

open Term in
elab "det_exec_of" fuel:num t:term : term => do
  let cfg1 ← elabTerm t (some (mkConst ``Cfg))
  unsafe elabDetExec fuel.getNat (← whnf cfg1)

section Tests

section Correctness

example : DetStep ⟨pl(fst((#1, #2))), default⟩ ⟨pl(#1), default⟩ :=
  det_step_of ⟨pl(fst((#1, #2))), default⟩

example : DetStep ⟨pl(snd((#1, #2))), default⟩ ⟨pl(#2), default⟩ :=
  det_step_of ⟨pl(snd((#1, #2))), default⟩

-- alloc: one step
example : ∃ cfg2, DetStep ⟨pl(alloc(#42)), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(alloc(#42)), default⟩⟩

-- load directly from a known state
def stateWith42 : State :=
  (default : State).update_heap (·.insert 0 ⟨pl(#42), .lit⟩)

example : ∃ cfg2, DetStep ⟨pl(!(#(BaseLit.loc (0 : Loc)))), stateWith42⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(!(#(BaseLit.loc (0 : Loc)))), stateWith42⟩⟩

-- case inl/inr
example : ∃ cfg2, DetStep ⟨pl(case inl(#1) | x => x + #10 | y => y), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(case inl(#1) | x => x + #10 | y => y), default⟩⟩

example : ∃ cfg2, DetStep ⟨pl(case inr(#2) | x => x | y => y + #10), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(case inr(#2) | x => x | y => y + #10), default⟩⟩

-- (fun x, x + #1) #2  steps by beta reduction
example : ∃ cfg2, DetStep ⟨pl((fun x, x + #1) #2), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl((fun x, x + #1) #2), default⟩⟩

example : DetStep ⟨pl(~#true), default⟩ ⟨pl(#false), default⟩ :=
  det_step_of ⟨pl(~#true), default⟩

example : ∃ cfg2, DetStep ⟨pl(-#5), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(-#5), default⟩⟩

example : DetStep ⟨pl(#1 + #2), default⟩ ⟨pl(#3), default⟩ :=
  det_step_of ⟨pl(#1 + #2), default⟩

example : DetStep ⟨pl(#10 - #3), default⟩ ⟨pl(#7), default⟩ :=
  det_step_of ⟨pl(#10 - #3), default⟩

example : DetStep ⟨pl(if #true then #1 else #2), default⟩ ⟨pl(#1), default⟩ :=
  det_step_of ⟨pl(if #true then #1 else #2), default⟩

example : DetStep ⟨pl(if #false then #1 else #2), default⟩ ⟨pl(#2), default⟩ :=
  det_step_of ⟨pl(if #false then #1 else #2), default⟩

example : DetStep ⟨pl(#1 + fst((#2, #3))), default⟩ ⟨pl(#1 + #2), default⟩ :=
  det_step_of ⟨pl(#1 + fst((#2, #3))), default⟩

end Correctness

section Synthesis

example : ∃ cfg2, DetStep ⟨pl(#1 + fst((#2, #3))), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(#1 + fst((#2, #3))), default⟩⟩

example : ∃ cfg2, DetStep ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩ cfg2 :=
  ⟨_, det_step_of ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩⟩

example : ∃ n cfg2, DetExec n ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 2 _⟩

example : ∃ n cfg2, DetExec n ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 3 _⟩

-- binop + fst: three steps: fst, fst, then binop evaluation
example : ∃ n cfg2, DetExec n ⟨pl(fst((#1, #2)) + fst((#3, #4))), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 5 _⟩

-- function application followed by arithmetic: (fun x, x * #2) #5 →* #10
example : ∃ n cfg2, DetExec n ⟨pl((fun x, x * #2) #5), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 5 _⟩

-- conditional branch: if #true then #1 + #2 else #99 →* #3
example : ∃ n cfg2, DetExec n ⟨pl(if #true then #1 + #2 else #99), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 5 _⟩

-- sum type dispatch: case inl(#3) | x => x + #1 | y => y →* #4
example : ∃ n cfg2, DetExec n ⟨pl(case inl(#3) | x => x + #1 | y => y), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 5 _⟩

-- nested: snd((fst((#1, #2)), #3)) →* #3 (two steps: inner fst, then snd)
example : ∃ n cfg2, DetExec n ⟨pl(snd((fst((#1, #2)), #3))), default⟩ cfg2 :=
  ⟨_, _, det_exec_of 5 _⟩

end Synthesis
end Tests
