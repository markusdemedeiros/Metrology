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

/-- `twp_pure` β-reduces `(fun x, x) #1` at the top level (`K = []`) and auto-cleans the
`open'`, leaving `tglWp E #1 Φ`. -/
example (E : CoPset) (Φ : Val rT → IProp GF) :
    ⊢@{IProp GF} tglWp E pl((fun x, x) #1) Φ := by
  twp_pure pl((fun x, x) #1)
  show ⊢@{IProp GF} tglWp E pl(#1) Φ
  sorry

/-- End-to-end (no `sorry`): `twp_pures` β-reduces `(fun x, x) #1` and evaluates the
`fst`, reaching the value `#1`; `twp_value` then discharges the value postcondition. -/
example (E : CoPset) :
    ⊢@{IProp GF} tglWp E pl(fst(((fun x, x) #1, #2)))
      (fun w : Val rT => iprop(⌜w = ⟨.lit (.int 1), IsVal.lit⟩⌝)) := by
  twp_pures
  twp_value
  ipureintro; rfl

/-- `twp_pure` now also handles computed-result redexes: `#1 + #2` evaluates to `#3`
via `BinOp.eval` (the side condition `… ∧ op.eval = some 3` is discharged by `rfl`). -/
example (E : CoPset) :
    ⊢@{IProp GF} tglWp E pl(#1 + #2)
      (fun w : Val rT => iprop(⌜w = ⟨.lit (.int 3), IsVal.lit⟩⌝)) := by
  twp_pure pl(#1 + #2)
  twp_value
  ipureintro; rfl

end TotalEris
end ProbLang
