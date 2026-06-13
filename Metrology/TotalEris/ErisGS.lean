module

public import Metrology.TotalEris.Glm
public import Metrology.Iris.AppProgram
public import Metrology.Iris.ErrorCredits

@[expose] public section

/-!
# `erisGS` — concrete ghost state for Eris

Port of `clutch/theories/eris/primitive_laws.v` lines 12-37. Bundles:

* `AppGS` — the heap + tape ghost-map state (defined in
  `Metrology/Iris/AppProgram.lean`; reused as-is since the eris and
  approxis state-shape coincide on the LHS-only side).
* `ECGS` — error-credit ghost state (defined in
  `Metrology/Iris/ErrorCredits.lean`; the `↯ ε` notation lives there).
* `InvGS_gen` — invariants (from Iris-Lean).

Provides the canonical `ErisWpGS` instance with
`stateInterp σ := appStateAuth σ` and `errInterp ε := ecAuth ε`.

The `↦` (heap pointsto) and `↪ₐ` (tape pointsto) notations come from
`Metrology/Iris/AppProgram.lean`; the `●↯` (error auth) notation comes
from `Metrology/Iris/ErrorCredits.lean`. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang

namespace ProbLang


namespace TotalEris


/-- Concrete ghost-state class for Eris.

Mirrors `Metrology.Approxis.ApproxisGS` minus the spec-side `SpecGS`
(Eris is unary). Uses `extends` via field projections rather than
nested `extends`-clauses, to avoid Lean's diamond-inheritance field
collapse — see the comment in `ApproxisGS`. -/
class ErisGS (rT : outParam (Type _)) [ProbLang.ProbLangℝ rT] (hlc : outParam HasLC) (GF : BundledGFunctors) where
  appGS : AppGS rT GF
  ecGS  : ECGS GF
  invGS : InvGS_gen hlc GF

attribute [reducible, instance] ErisGS.appGS ErisGS.ecGS ErisGS.invGS

section ErisInstance

variable {rT : Type _} [ProbLang.ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

@[reducible]
noncomputable instance erisWpGS_of_components : ErisWpGS (rT := rT) GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  errInterp ε := ecAuth ε

/-! ### Unfolding lemmas -/

@[simp] theorem erisWpGS_stateInterp_eq :
    (ErisWpGS.stateInterp (rT := rT) : State rT → IProp GF) = appStateAuth := rfl

@[simp] theorem erisWpGS_errInterp_eq :
    (ErisWpGS.errInterp (rT := rT) : ENNReal → IProp GF) = ecAuth := rfl

end ErisInstance

end TotalEris
end ProbLang
