module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals

@[expose] public section

/-!
# Smoke tests for real comparison in `BinOp.eval` (proof-phase task #1)

Confirms the `ProbLangℝ` real-order extension does what the samplers need:
the `.lt`/`.le` real arms of `BinOp.eval` fire, and `twp_pure` can step a
*symbolic* real comparison `r1 < r2` (the shape every sampler branches on).
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-- The real `<` arm of `BinOp.eval` fires definitionally. -/
example (r1 r2 : ℝ) :
    BinOp.eval (rT := ℝ) .lt (.lit (.real r1)) (.lit (.real r2))
      = some (.lit (.bool (ProbLangℝ.realLt r1 r2))) := rfl

/-- The real `≤` arm fires definitionally. -/
example (r1 r2 : ℝ) :
    BinOp.eval (rT := ℝ) .le (.lit (.real r1)) (.lit (.real r2))
      = some (.lit (.bool (ProbLangℝ.realLe r1 r2))) := rfl

/-- At `ℝ`, the comparison data connects to the mathematical order (`rfl`). -/
example (r1 r2 : ℝ) : ProbLangℝ.realLt r1 r2 = decide (r1 < r2) := rfl

/-- **The operational test:** `twp_pure` steps a symbolic real comparison
`r1 < r2`, leaving the boolean `ProbLangℝ.realLt r1 r2` for the proof to case on
— exactly what `DecrTrial`/`LeHalf`/`Bii`/… need. -/
example (E : CoPset) (r1 r2 : ℝ) (Φ : Val ℝ → IProp GF) :
    ⊢@{IProp GF} tglWp E pl(#(.real r1) < #(.real r2)) Φ := by
  twp_pure pl(#(.real r1) < #(.real r2))
  show ⊢@{IProp GF} tglWp E pl(#(.bool (ProbLangℝ.realLt r1 r2))) Φ
  sorry

end
end Examples
end TotalEris
end ProbLang
