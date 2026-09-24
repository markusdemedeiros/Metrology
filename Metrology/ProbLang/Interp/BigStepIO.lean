module

public import Metrology.ProbLang.BigStep
public import Metrology.ProbLang.EnvStep
public import Metrology.ProbLang.Comp

@[expose] public section

/-! # The ProbLang interpreter

`run` executes the environment machine. Its three loops (`runEval`, `runApply`, `runRet`)
are `evalK`, `applyK` and `resumeK` read through `ioStepOps`: the same step functions whose
`stepOps` reading is proved correct. `EnvStepEquiv.envBig_eval_closed` shows the machine's
measure semantics equals `limExec` on closed programs.

The frame stack lives on the heap, so an object-level tail call pushes nothing and deep
non-tail recursion grows only that stack, never the native one. After inlining, the three
loops call each other in tail position.

The code to check by hand is `ioStepOps` and `runRet`: each operation must mean what
`Step.interp` says the corresponding `Step` constructor means.

`runSubst` executes the substitution evaluator `bigStepF` through `Comp` trees and `drive`.
It is slower and serves as a reference for differential testing.
-/

namespace ProbLang
namespace Interp

/-- A source of samples for `urand`, meant to draw from `ProbLangℝ.unifUnit`. -/
class UnifUnitSampler (rT : Type _) where
  sample : IO rT

variable {rT : Type} [ProbLangℝ rT] [UnifUnitSampler rT] {C R : Type}

/-- Run `c` with recursive calls handled by `step`, then pass its result to the
continuations `ks`, the last one first. Stuck terms and `fail` raise an `IO` error. -/
@[specialize]
partial def drive (step : C → Comp rT C R) (c : Comp rT C R) (ks : Array (R → Comp rT C R)) :
    IO R := do
  match c with
  | .call x => drive step (step x) ks
  | .bind c k => drive step c (ks.push k)
  | .ret r =>
    match ks.back? with
    | none => return r
    | some k => drive step (k r) ks.pop
  | .stuck msg => throw (IO.userError s!"stuck: {msg}")
  | .sample z k =>
    let n : Int ← if 0 < z then pure (← IO.rand 0 (z - 1).toNat) else pure (-1)
    drive step (k n) ks
  | .sampleReal k =>
    let r ← UnifUnitSampler.sample
    drive step (k r) ks

/-- The interpreter's `StepOps`, given its three loops. The frame stack `ks` lives on the
heap: `evalThen` pushes a frame, and `runRet` pops the next one. -/
@[inline] def ioStepOps
    (runEval : Env rT → Exp rT → State rT → Array (Frame rT) → IO (RCfg rT))
    (runApply : RVal rT → RVal rT → State rT → Array (Frame rT) → IO (RCfg rT))
    (runRet : RVal rT → State rT → Array (Frame rT) → IO (RCfg rT)) :
    StepOps rT (Array (Frame rT) → IO (RCfg rT)) where
  ret v σ ks := runRet v σ ks
  eval env e σ ks := runEval env e σ ks
  evalThen env e σ f ks := runEval env e σ (ks.push f)
  apply f v σ ks := runApply f v σ ks
  stuck msg _ := throw (IO.userError s!"stuck: {msg}")
  uniform z σ ks := do
    -- `Cfg.uniform`: uniform on `[0, z)`, or `-1` when `z ≤ 0`.
    let n : Int ← if 0 < z then pure (← IO.rand 0 (z - 1).toNat) else pure (-1)
    runRet (.lit (.int n)) σ ks
  uniformReal σ ks := do
    let r ← UnifUnitSampler.sample
    runRet (.lit (.real r)) σ ks

mutual
/-- Evaluate `e` under `env`, then resume the frames `ks`. -/
partial def runEval (env : Env rT) (e : Exp rT) (σ : State rT) (ks : Array (Frame rT)) :
    IO (RCfg rT) :=
  evalK (ioStepOps runEval runApply runRet) env e σ ks

/-- Apply `f` to `v`, then resume the frames `ks`. -/
partial def runApply (f v : RVal rT) (σ : State rT) (ks : Array (Frame rT)) : IO (RCfg rT) :=
  applyK (ioStepOps runEval runApply runRet) f v σ ks

/-- Resume the frames `ks` with the value `v`, the last frame first. -/
partial def runRet (v : RVal rT) (σ : State rT) (ks : Array (Frame rT)) : IO (RCfg rT) :=
  match ks.back? with
  | none => return ⟨v, σ⟩
  | some f => resumeK (ioStepOps runEval runApply runRet) f v σ ks.pop
end

/-- Run the environment machine on a configuration. -/
def run : EnvCfg rT → IO (RCfg rT)
  | .eval env e σ => runEval env e σ #[]
  | .apply f v σ => runApply f v σ #[]
  | .resume f v σ => resumeK (ioStepOps runEval runApply runRet) f v σ #[]

/-- Run a closed expression from the empty state and read its value back. -/
def eval (e : Exp rT) : IO (Exp rT) := do
  let r ← run (.eval [] e default)
  return r.val.rb

/-- `bigStepF` read into `Comp`. -/
def compOps : EvalOps rT (Comp rT (Cfg rT) (Cfg rT)) where
  ret := .ret
  bind := .bind
  stuck := .stuck
  uniform z σ := .sample z fun n => .ret ⟨.lit (.int n), σ⟩
  uniformReal σ := .sampleReal fun r => .ret ⟨.lit (.real r), σ⟩

/-- Run the substitution evaluator `bigStepF` on a configuration. -/
def runSubst (ρ : Cfg rT) : IO (Cfg rT) :=
  drive (bigStepF compOps .call) (.call ρ) #[]

end Interp
end ProbLang
