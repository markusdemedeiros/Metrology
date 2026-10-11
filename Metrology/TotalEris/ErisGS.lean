module

public import Metrology.TotalEris.Glm
public import Metrology.Iris.AppProgram
public import Metrology.Iris.ErrorCredits
public import Metrology.ProbLang.Reals
public import Iris.Algebra.Auth

@[expose] public section

local stepindex Nat

/-! # Eris Ghost State Definitions -/

open Iris Auth

namespace ProbLang

namespace TotalEris

/-- Concrete ghost-state class for Eris. -/
class ErisGS (rT : outParam (Type _)) [LawfulProbLangℝ rT] (hlc : outParam HasLC)
    (GF : BundledGFunctors) where
  appGS : AppGS rT GF
  ecGS  : ECGS GF
  invGS : InvGS_gen hlc GF

attribute [reducible, instance] ErisGS.appGS ErisGS.ecGS ErisGS.invGS

section ErisInstance

variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

@[reducible]
noncomputable instance erisWpGS_of_components : ErisWpGS (rT := rT) GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  errInterp ε := ecAuth ε

/-! ### Unfolding lemmas -/

@[simp] theorem erisWpGS_stateInterp_eq :
    (ErisWpGS.stateInterp : State rT → IProp GF) = appStateAuth := rfl

@[simp] theorem erisWpGS_errInterp_eq :
    (ErisWpGS.errInterp (rT := rT) : ENNReal → IProp GF) = ecAuth := rfl

end ErisInstance

noncomputable def erisGF : BundledGFunctors.{0,0,0} := fun
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset)⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (Auth ErrorCredit)⟩
  | 5 => ⟨constOF (SpecHeap ℝ)⟩
  | 6 => ⟨constOF SpecTapes⟩
  | _ => ⟨constOF Unit⟩

instance : WsatGpreS erisGF where
  inv := { τ := 0, transp := by unfold erisGF; rfl }
  enabled := { τ := 1, transp := by unfold erisGF; rfl }
  disabled := { τ := 2, transp := by unfold erisGF; rfl }

instance : LcGpreS erisGF where
  lc_elem := { τ := 3, transp := by unfold erisGF; rfl }

instance : InvGpreS erisGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance : ECPreGS erisGF where
  ec := { τ := 4, transp := by unfold erisGF; rfl }

instance : AppPreGS ℝ erisGF where
  heap := { τ := 5, transp := by unfold erisGF; rfl }
  tapes := { τ := 6, transp := by unfold erisGF; rfl }

end TotalEris
end ProbLang
