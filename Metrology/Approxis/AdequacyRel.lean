import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Model
import Metrology.Approxis.Adequacy
import Iris.Algebra.Auth
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Instances.Lib.FUpd

/-! # Relational adequacy: bridging parametric `refines` to an `AddCoupl` on `limExec`. -/

namespace ProbLang

open Iris Iris.BI Iris.ProofMode OFE COFE Iris.Std DisjointLeibnizSet Auth HeapView
open ProbLang.AdequacyHelpers ProbLang.ApproxisWpGS

theorem refines_coupling {GF : BundledGFunctors}
    [IPre : AppPreGS GF] [ISPre : SpecPreGS GF] [IECPre : ECPreGS GF]
    [IInvPre : InvGpreS GF] [INaPre : NaInvG GF]
    (A : ∀ (_ : ApproxisRGS false GF), lrel GF)
    (φ : Val → Val → Prop) (e e' : Exp) (σ σ' : State)
    (HA : ∀ (IR : ApproxisRGS false GF) (v v' : Val),
      ⊢@{IProp GF} iprop((A IR).car v v' -∗ ⌜φ v v'⌝))
    (Hlog : ∀ (IR : ApproxisRGS false GF),
      ⊢@{IProp GF} refines (hlc := false) (GF := GF) ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) ((limExec ⟨e, σ⟩).map (·.expr))
        ((limExec ⟨e', σ'⟩).map (·.expr)) := by
  apply wp_adequacy_error_lim (GF := GF) e e' σ σ' 0 φ
  intro IGS ε' Hε'pos
  iintro He' Herr
  imod (Iris.NonAtomicInvariant.alloc (GF := GF)) with HnaEx
  icases HnaEx with ⟨%γ, Htok⟩
  set IR : ApproxisRGS false GF :=
    { approxisGS := IGS
      naInvG := INaPre
      nais := γ }
  have HlogIR : (⊢@{IProp GF} refines (hlc := false) (GF := GF) ⊤ e e' (A IR)) := Hlog IR
  ihave Hlog' := HlogIR
  ihave Hwp := refines_unfold (E := ⊤) (e := e) (e' := e') (A := A IR) $$ Hlog'
  have hf : e' = Ectx.fill ([] : Ectx) e' := rfl
  ihave He'' : iprop(⤇ Ectx.fill ([] : Ectx) e') $$ [He']
  · rw [← hf]; iexact He'
  ispecialize Hwp $$ %([] : Ectx) %ε' He'' Htok Herr %Hε'pos
  iapply (wp_mono
    (Φ := fun v => iprop(∃ (v' : Val) (ε'' : ENNReal),
      (⤇ Ectx.fill ([] : Ectx) v'.1) ∗ (naOwnP ⊤) ∗ (↯ ε'') ∗
      (⌜(0 : ENNReal) < ε''⌝) ∗ (A IR).car v v'))
    (Ψ := fun v => iprop(∃ v' : Val, ⤇ Exp.ofVal v' ∗ ⌜φ v v'⌝)))
  case HΦ =>
    intro v
    iintro Hpost
    icases Hpost with ⟨%v', %ε'', Hspec, Hna, Herr', %Hpos, HA_v⟩
    iexists v'
    isplitl [Hspec]
    · have hf : (iprop(⤇ Ectx.fill ([] : Ectx) v'.1) : IProp GF) =
                iprop(⤇ Exp.ofVal v') := rfl
      rw [← hf]; iexact Hspec
    · ihave Hbridge := HA IR v v'
      ihave Hphi := Hbridge $$ HA_v
      iexact Hphi
  iexact Hwp

/-! ### Concrete `BundledGFunctors` for the OTP example -/

/-- Concrete model `BundledGFunctors` for OTP/Approxis. Slot 7/8 (spec heap/tapes)
are distinct from slot 4/5 (program heap/tapes) to prevent γ-aliasing. -/
noncomputable def otpSigma : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF, by infer_instance⟩
  | 1  => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3  => ⟨AuthURF (F := ℕ+) (constOF Credit), by infer_instance⟩
  | 4  => ⟨constOF SpecHeap, by infer_instance⟩
  | 5  => ⟨constOF SpecTapes, by infer_instance⟩
  | 6  => ⟨constOF SpecProg, by infer_instance⟩
  | 7  => ⟨constOF SpecHeap, by infer_instance⟩
  | 8  => ⟨constOF SpecTapes, by infer_instance⟩
  | 9  => ⟨constOF (Auth ℕ+ ErrorCredit), by infer_instance⟩
  | 10 => ⟨NaInvF, by infer_instance⟩
  | _  => ⟨constOF Unit, by infer_instance⟩

/-! ### PreGS instances for `otpSigma` -/

instance otpSigma_WsatGpreS : WsatGpreS otpSigma where
  inv := { τ := 0, transp := by unfold otpSigma; rfl }
  enabled := { τ := 1, transp := by unfold otpSigma; rfl }
  disabled := { τ := 2, transp := by unfold otpSigma; rfl }

instance otpSigma_LcGpreS : LcGpreS otpSigma where
  lc_elem := { τ := 3, transp := by unfold otpSigma; rfl }

instance otpSigma_InvGpreS : InvGpreS otpSigma where
  toWsatGpreS := otpSigma_WsatGpreS
  toLcGpreS := otpSigma_LcGpreS

instance otpSigma_AppPreGS : AppPreGS otpSigma where
  heap := { τ := 4, transp := by unfold otpSigma; rfl }
  tapes := { τ := 5, transp := by unfold otpSigma; rfl }

instance otpSigma_SpecPreGS : SpecPreGS otpSigma where
  prog := { τ := 6, transp := by unfold otpSigma; rfl }
  heap := { τ := 7, transp := by unfold otpSigma; rfl }
  tapes := { τ := 8, transp := by unfold otpSigma; rfl }

instance otpSigma_ECPreGS : ECPreGS otpSigma where
  ec := { τ := 9, transp := by unfold otpSigma; rfl }

instance otpSigma_NaInvG : NaInvG otpSigma where
  inv := { τ := 10, transp := by unfold otpSigma; rfl }

end ProbLang
