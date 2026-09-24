module

public import Metrology.ProbLang.BigStep

@[expose] public section

/-! # The ProbLang interpreter

`run` is the fixed point of `bigStepF` read in `IO`. It is the same evaluator whose least
fixed point in the Giry monad is `bigStep`, which `BigStepEquiv.lean` proves equal to
`limExec`. Only the effects differ, and `ioOps` lists all of them.
-/

namespace ProbLang
namespace Interp

/-- A source of samples for `urand`, meant to draw from `ProbLangℝ.unifUnit`. -/
class UnifUnitSampler (rT : Type _) where
  sample : IO rT

variable {rT : Type _} [ProbLangℝ rT] [UnifUnitSampler rT]

/-- `bigStepF` read in `IO`. Stuck terms and `fail` raise an `IO` error. -/
def ioOps : EvalOps rT (IO (Cfg rT)) where
  ret := pure
  bind := (· >>= ·)
  stuck msg := throw (IO.userError s!"stuck: {msg}")
  uniform z σ :=
    if 0 < z then do
      let n ← IO.rand 0 (z - 1).toNat
      return ⟨.lit (.int n), σ⟩
    else return ⟨.lit (.int (-1)), σ⟩
  uniformReal σ := do
    let r ← UnifUnitSampler.sample
    return ⟨.lit (.real r), σ⟩

/-- Run a configuration to a final configuration. -/
partial def run (ρ : Cfg rT) : IO (Cfg rT) :=
  bigStepF ioOps run ρ

/-- Run an expression from the empty state and return its value. -/
def eval (e : Exp rT) : IO (Exp rT) := do
  let ⟨v, _⟩ ← run ⟨e, default⟩
  return v

end Interp
end ProbLang
