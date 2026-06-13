module

public import Metrology.TotalEris

@[expose] public section

/-!
# Smoke tests for the elaborator-based `twp_*` tactics (`WpTactics.lean`)
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang
namespace TotalEris

variable {rT : Type _} [ProbLang.ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- `twp_bind` auto-discovers the evaluation context `K = [.fst]` and refocuses the
goal onto the inner `alloc` redex — no explicit `K` supplied. -/
example (E : CoPset) (Φ : Val rT → IProp GF) :
    ⊢@{IProp GF} tglWp E pl(fst(alloc(#1))) Φ := by
  twp_bind pl(alloc(#1))
  -- `twp_bind` discovered `K = [.fst]` and refocused; the goal is now defeq to
  -- `tglWp E (alloc #1) (fun w => tglWp E (fst (ofVal w)) Φ)`, as this `show` checks.
  show ⊢@{IProp GF} tglWp E pl(alloc(#1))
    (fun w => tglWp E pl(fst({Exp.ofVal w})) Φ)
  sorry

end TotalEris
end ProbLang
