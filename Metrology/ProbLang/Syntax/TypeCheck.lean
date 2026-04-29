module

public import Metrology.ProbLang.Syntax.Types

@[expose] public section

/-!
# `typecheck` bidirectional elaborator for ProbLang

A bidirectional typechecker realized as a term/tactic elaborator. Used at a
term position with expected type `Typed Γ e τ`, it synthesizes a proof of
that judgment by recursing on the head of `e`.

```
example : Typed Γ e τ := typecheck
example : Typed Γ e τ := by typecheck
```

## Modes

- `checkMVar mvar` — `mvar : Typed Γ e τ` with `τ` fixed; applies the
  constructor whose conclusion matches `e`'s head, recurses.
- `synth Γ e` — returns `(τ, proof : Typed Γ e τ)`; the type is determined
  by `e`'s head.
- Switch: `check` on a synth-mode head calls `synth`, unifies the returned
  type with the expected one, and uses the returned proof.

## Coverage

Check-mode heads:  pair, inl, inr, fail
Synth-mode heads:  var, lit, fst, snd
TODO:              binop, unop, cond, case, letrec, app,
                   alloc, load, store, tape, rand, scrut
TODO (non-alg.):   tfold, tunfold, tpack, tunpack, tlam, tapp
-/

namespace ProbLang

open Lean Elab Term Tactic Meta

/-- Decompose `Typed Γ e τ`. -/
private def asTypedGoal (goal : Expr) : TermElabM (Expr × Expr × Expr) := do
  let goal ← Meta.whnf goal
  let some (Γ, e, τ) := goal.app3? ``Typed
    | throwError "typecheck: expected type is not `Typed Γ e τ`:{indentExpr goal}"
  return (Γ, ← Meta.whnf e, τ)

mutual

/-- Synth mode: build a proof of `Typed Γ e τ` for some type `τ` determined
    by `e`. Returns the inferred `τ` and the proof. -/
partial def synth (Γ e : Expr) : TermElabM (Expr × Expr) := do
  let e ← Meta.whnf e
  match e.getAppFn.constName? with
  | some ``Exp.fvar =>
      -- We don't know τ a priori; leave it as a metavariable and let the
      -- `rfl` for `Γ x = some τ` pin it down.
      let τ ← mkFreshExprMVar (mkConst ``Ty)
      let lookupTy ← mkAppM ``Eq #[← mkAppM' Γ #[e.getArg! 0], ← mkAppM ``Option.some #[τ]]
      let lookup ← mkFreshExprMVar lookupTy
      lookup.mvarId!.refl
      let proof ← mkAppM ``Typed.fvar #[lookup]
      return (← instantiateMVars τ, proof)
  | some ``Exp.lit =>
      let arg := (e.getArg! 0).consumeMData
      match arg.getAppFn.constName? with
      | some ``BaseLit.int  =>
          let z := arg.getArg! 0
          return (mkConst ``Ty.int,  ← mkAppOptM ``Typed.lit_int  #[Γ, z])
      | some ``BaseLit.bool =>
          let b := arg.getArg! 0
          return (mkConst ``Ty.bool, ← mkAppOptM ``Typed.lit_bool #[Γ, b])
      | some ``BaseLit.unit =>
          return (mkConst ``Ty.unit, ← mkAppOptM ``Typed.lit_unit #[Γ])
      | _ => throwError "typecheck/synth: unsupported literal {arg}"
  | some ``Exp.fst =>
      let τ1 ← mkFreshExprMVar (mkConst ``Ty)
      let τ2 ← mkFreshExprMVar (mkConst ``Ty)
      let τprod ← mkAppM ``Ty.prod #[τ1, τ2]
      let subGoal ← mkAppM ``Typed #[Γ, e.getArg! 0, τprod]
      let subMvar ← mkFreshExprMVar subGoal
      checkMVar subMvar.mvarId!
      return (← instantiateMVars τ1, ← mkAppM ``Typed.fst #[subMvar])
  | some ``Exp.snd =>
      let τ1 ← mkFreshExprMVar (mkConst ``Ty)
      let τ2 ← mkFreshExprMVar (mkConst ``Ty)
      let τprod ← mkAppM ``Ty.prod #[τ1, τ2]
      let subGoal ← mkAppM ``Typed #[Γ, e.getArg! 0, τprod]
      let subMvar ← mkFreshExprMVar subGoal
      checkMVar subMvar.mvarId!
      return (← instantiateMVars τ2, ← mkAppM ``Typed.snd #[subMvar])
  | some c => throwError "typecheck/synth: TODO `{c}` is not yet in synth mode"
  | none   => throwError "typecheck/synth: cannot determine head:{indentExpr e}"

/-- Check mode: close `mvar : Typed Γ e τ`. -/
partial def checkMVar (mvar : MVarId) : TermElabM Unit := mvar.withContext do
  let (Γ, e, τ) ← asTypedGoal (← mvar.getType)
  let checkSub (e' τ' : Expr) : TermElabM Expr := do
    let sub ← mkFreshExprMVar (← mkAppM ``Typed #[Γ, e', τ'])
    checkMVar sub.mvarId!
    return sub
  let τ ← Meta.whnf τ
  match e.getAppFn.constName? with
  -- Check-mode heads: rule determined by the expected type's shape.
  | some ``Exp.pair =>
      let some (τ1, τ2) := τ.app2? ``Ty.prod
        | throwError "typecheck/check pair: expected a product type, got{indentExpr τ}"
      let h1 ← checkSub (e.getArg! 0) τ1
      let h2 ← checkSub (e.getArg! 1) τ2
      mvar.assign (← mkAppM ``Typed.pair #[h1, h2])
  | some ``Exp.inl =>
      let some (τ1, τ2) := τ.app2? ``Ty.sum
        | throwError "typecheck/check inl: expected a sum type, got{indentExpr τ}"
      let h ← checkSub (e.getArg! 0) τ1
      mvar.assign (← mkAppOptM ``Typed.inl #[Γ, e.getArg! 0, τ1, τ2, h])
  | some ``Exp.inr =>
      let some (τ1, τ2) := τ.app2? ``Ty.sum
        | throwError "typecheck/check inr: expected a sum type, got{indentExpr τ}"
      let h ← checkSub (e.getArg! 0) τ2
      mvar.assign (← mkAppOptM ``Typed.inr #[Γ, e.getArg! 0, τ1, τ2, h])
  -- `.fail` removed from the type system; would need a stuck-typing rule.
  -- Synth-mode heads: call synth and unify.
  | some ``Exp.fvar | some ``Exp.lit | some ``Exp.fst | some ``Exp.snd =>
      let (τ', proof) ← synth Γ e
      unless ← isDefEq τ τ' do
        throwError "typecheck/switch: inferred type{indentExpr τ'}\n\
                    does not match expected{indentExpr τ}"
      mvar.assign proof
  | some c => throwError "typecheck/check: TODO unsupported expression head `{c}`"
  | none   => throwError "typecheck/check: cannot determine head:{indentExpr e}"

end

elab "typecheck" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let mvar ← mkFreshExprMVar expectedType
  checkMVar mvar.mvarId!
  instantiateMVars mvar

elab "typecheck" : tactic => do
  let mvar ← getMainGoal
  Term.TermElabM.run' (checkMVar mvar)

section Examples

example : Typed Tctx.empty (.lit (.int 42)) .int := typecheck
-- `Typed Tctx.empty .fail .bool` no longer holds: `Typed.fail` was removed.
example : Typed Tctx.empty (.pair (.lit (.int 1)) (.lit .unit)) (.prod .int .unit) :=
  typecheck
example : Typed (Tctx.empty.insert "x" .bool) (.fvar "x") .bool := typecheck
example : Typed Tctx.empty (.inl (.lit (.bool true))) (.sum .bool .int) := typecheck

-- Synth-driven: `fst` pulls the product type through.
example : Typed Tctx.empty
    (.fst (.pair (.lit (.int 7)) (.lit (.bool false)))) .int := typecheck

example : Typed Tctx.empty (.lit (.int 42)) .int := by typecheck

end Examples

end ProbLang
